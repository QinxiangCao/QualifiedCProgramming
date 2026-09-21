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
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 10000)) (PreH7 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH8 : ((Zlength (times)) = m_pre)) (PreH9 : ((Zlength (origins)) = m_pre)) (PreH10 : ((Zlength (destinations)) = m_pre)) (PreH11 : (Forall (Z.le (0)) dist )) (PreH12 : (Forall (Z.ge (100)) dist )) (PreH13 : (Forall (Z.le (0)) times )) (PreH14 : (Forall (Z.ge (100000)) times )) (PreH15 : (Forall (Z.le (1)) origins )) (PreH16 : (Forall (Z.ge (n_pre)) destinations )) (PreH17 : (Forall2 Z.lt origins destinations )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.seg ( &( "late" ) ) 0 i latest_prefix )
  **  (IntArray.undef_seg ( &( "late" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (IntArray.seg ( &( "late" ) ) 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "late" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (IntArray.seg ( &( "off" ) ) 0 (i + 1 ) (app (counts_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "off" ) ) (i + 1 ) n_pre )
  **  (IntArray.seg ( &( "late" ) ) 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "late" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.seg ( &( "late" ) ) 0 i latest_prefix )
  **  (IntArray.undef_seg ( &( "late" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i origins 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i origins 0) - 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i origins 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i origins 0) - 1 )) ”
).

Definition solve_safety_wit_6_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i origins 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_6_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((Znth i origins 0) - 1 )) ”
.

Definition solve_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
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
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
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
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
).

Definition solve_safety_wit_8_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
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
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_8_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
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
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
.

Definition solve_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
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
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_10 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
).

Definition solve_safety_wit_10_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_10_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
.

Definition solve_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_12 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
).

Definition solve_safety_wit_12_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_12_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) ”
.

Definition solve_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
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
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0) + 1 )) (counts)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
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
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_17 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_18 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur >= (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 10000)) (PreH12 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (times)) = m_pre)) (PreH14 : ((Zlength (origins)) = m_pre)) (PreH15 : ((Zlength (destinations)) = m_pre)) (PreH16 : (Forall (Z.le (0)) dist )) (PreH17 : (Forall (Z.ge (100)) dist )) (PreH18 : (Forall (Z.le (0)) times )) (PreH19 : (Forall (Z.ge (100000)) times )) (PreH20 : (Forall (Z.le (1)) origins )) (PreH21 : (Forall (Z.ge (n_pre)) destinations )) (PreH22 : (Forall2 Z.lt origins destinations )) (PreH23 : (0 <= k_pre)) (PreH24 : (k_pre <= 100000)) (PreH25 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_19 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 10000)) (PreH12 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (times)) = m_pre)) (PreH14 : ((Zlength (origins)) = m_pre)) (PreH15 : ((Zlength (destinations)) = m_pre)) (PreH16 : (Forall (Z.le (0)) dist )) (PreH17 : (Forall (Z.ge (100)) dist )) (PreH18 : (Forall (Z.le (0)) times )) (PreH19 : (Forall (Z.ge (100000)) times )) (PreH20 : (Forall (Z.le (1)) origins )) (PreH21 : (Forall (Z.ge (n_pre)) destinations )) (PreH22 : (Forall2 Z.lt origins destinations )) (PreH23 : (0 <= k_pre)) (PreH24 : (k_pre <= 100000)) (PreH25 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_20 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 10000)) (PreH12 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (times)) = m_pre)) (PreH14 : ((Zlength (origins)) = m_pre)) (PreH15 : ((Zlength (destinations)) = m_pre)) (PreH16 : (Forall (Z.le (0)) dist )) (PreH17 : (Forall (Z.ge (100)) dist )) (PreH18 : (Forall (Z.le (0)) times )) (PreH19 : (Forall (Z.ge (100000)) times )) (PreH20 : (Forall (Z.le (1)) origins )) (PreH21 : (Forall (Z.ge (n_pre)) destinations )) (PreH22 : (Forall2 Z.lt origins destinations )) (PreH23 : (0 <= k_pre)) (PreH24 : (k_pre <= 100000)) (PreH25 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_21 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur >= (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 10000)) (PreH12 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (times)) = m_pre)) (PreH14 : ((Zlength (origins)) = m_pre)) (PreH15 : ((Zlength (destinations)) = m_pre)) (PreH16 : (Forall (Z.le (0)) dist )) (PreH17 : (Forall (Z.ge (100)) dist )) (PreH18 : (Forall (Z.le (0)) times )) (PreH19 : (Forall (Z.ge (100000)) times )) (PreH20 : (Forall (Z.le (1)) origins )) (PreH21 : (Forall (Z.ge (n_pre)) destinations )) (PreH22 : (Forall2 Z.lt origins destinations )) (PreH23 : (0 <= k_pre)) (PreH24 : (k_pre <= 100000)) (PreH25 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_22 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i latest 0) + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i latest 0) + (Znth i dist 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i latest 0) + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i latest 0) + (Znth i dist 0) )) ”
).

Definition solve_safety_wit_22_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i latest 0) + (Znth i dist 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_22_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((Znth i latest 0) + (Znth i dist 0) )) ”
.

Definition solve_safety_wit_23 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((cur + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i dist 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((cur + (Znth i dist 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + (Znth i dist 0) )) ”
).

Definition solve_safety_wit_23_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((cur + (Znth i dist 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_23_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= (cur + (Znth i dist 0) )) ”
.

Definition solve_safety_wit_24 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_25 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_26 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_27 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_28 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (0 <= k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (latest)) = n_pre)) (PreH21 : ((Zlength (counts)) = n_pre)) (PreH22 : ((Zlength (arrivals)) = n_pre)) (PreH23 : (Forall (Z.le (0)) current_dist )) (PreH24 : (Forall (Z.ge (100)) current_dist )) (PreH25 : (Forall (Z.le (0)) latest )) (PreH26 : (Forall (Z.ge (100000)) latest )) (PreH27 : (Forall (Z.le (0)) counts )) (PreH28 : (Forall (Z.ge (m_pre)) counts )) (PreH29 : (Forall (Z.le (0)) arrivals )) (PreH30 : (Forall (Z.ge (200000)) arrivals )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_29 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : ((Zlength (arrivals)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (Forall (Z.le (0)) arrivals )) (PreH31 : (Forall (Z.ge (200000)) arrivals )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_30 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : ((Zlength (arrivals)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (Forall (Z.le (0)) arrivals )) (PreH31 : (Forall (Z.ge (200000)) arrivals )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solve_safety_wit_31 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : ((Zlength (arrivals)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (Forall (Z.le (0)) arrivals )) (PreH31 : (Forall (Z.ge (200000)) arrivals )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_32 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : ((Zlength (arrivals)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (Forall (Z.le (0)) arrivals )) (PreH31 : (Forall (Z.ge (200000)) arrivals )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_33 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (0 <= best)) (PreH7 : (best <= m_pre)) (PreH8 : ((-1) <= pos)) (PreH9 : (pos < i)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 10000)) (PreH14 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (times)) = m_pre)) (PreH16 : ((Zlength (origins)) = m_pre)) (PreH17 : ((Zlength (destinations)) = m_pre)) (PreH18 : (Forall (Z.le (0)) dist )) (PreH19 : (Forall (Z.ge (100)) dist )) (PreH20 : (Forall (Z.le (0)) times )) (PreH21 : (Forall (Z.ge (100000)) times )) (PreH22 : (Forall (Z.le (1)) origins )) (PreH23 : (Forall (Z.ge (n_pre)) destinations )) (PreH24 : (Forall2 Z.lt origins destinations )) (PreH25 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH26 : ((Zlength (latest)) = n_pre)) (PreH27 : ((Zlength (counts)) = n_pre)) (PreH28 : ((Zlength (arrivals)) = n_pre)) (PreH29 : (Forall (Z.le (0)) current_dist )) (PreH30 : (Forall (Z.ge (100)) current_dist )) (PreH31 : (Forall (Z.le (0)) latest )) (PreH32 : (Forall (Z.ge (100000)) latest )) (PreH33 : (Forall (Z.le (0)) counts )) (PreH34 : (Forall (Z.ge (m_pre)) counts )) (PreH35 : (Forall (Z.le (0)) arrivals )) (PreH36 : (Forall (Z.ge (200000)) arrivals )) (PreH37 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH38 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_34 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (0 < k)) (PreH2 : (k <= k_pre)) (PreH3 : (k_pre <= 100000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 1 ))) (PreH6 : (0 <= best)) (PreH7 : (best <= m_pre)) (PreH8 : ((-1) <= pos)) (PreH9 : (pos < i)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 10000)) (PreH14 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (times)) = m_pre)) (PreH16 : ((Zlength (origins)) = m_pre)) (PreH17 : ((Zlength (destinations)) = m_pre)) (PreH18 : (Forall (Z.le (0)) dist )) (PreH19 : (Forall (Z.ge (100)) dist )) (PreH20 : (Forall (Z.le (0)) times )) (PreH21 : (Forall (Z.ge (100000)) times )) (PreH22 : (Forall (Z.le (1)) origins )) (PreH23 : (Forall (Z.ge (n_pre)) destinations )) (PreH24 : (Forall2 Z.lt origins destinations )) (PreH25 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH26 : ((Zlength (latest)) = n_pre)) (PreH27 : ((Zlength (counts)) = n_pre)) (PreH28 : ((Zlength (arrivals)) = n_pre)) (PreH29 : (Forall (Z.le (0)) current_dist )) (PreH30 : (Forall (Z.ge (100)) current_dist )) (PreH31 : (Forall (Z.le (0)) latest )) (PreH32 : (Forall (Z.ge (100000)) latest )) (PreH33 : (Forall (Z.le (0)) counts )) (PreH34 : (Forall (Z.ge (m_pre)) counts )) (PreH35 : (Forall (Z.le (0)) arrivals )) (PreH36 : (Forall (Z.ge (200000)) arrivals )) (PreH37 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH38 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_35 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 1 ))) (PreH7 : (0 <= best)) (PreH8 : (best <= m_pre)) (PreH9 : ((-1) <= pos)) (PreH10 : (pos < i)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (latest)) = n_pre)) (PreH28 : ((Zlength (counts)) = n_pre)) (PreH29 : ((Zlength (arrivals)) = n_pre)) (PreH30 : (Forall (Z.le (0)) current_dist )) (PreH31 : (Forall (Z.ge (100)) current_dist )) (PreH32 : (Forall (Z.le (0)) latest )) (PreH33 : (Forall (Z.ge (100000)) latest )) (PreH34 : (Forall (Z.le (0)) counts )) (PreH35 : (Forall (Z.ge (m_pre)) counts )) (PreH36 : (Forall (Z.le (0)) arrivals )) (PreH37 : (Forall (Z.ge (200000)) arrivals )) (PreH38 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH39 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_36 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest)) = n_pre)) (PreH29 : ((Zlength (counts)) = n_pre)) (PreH30 : ((Zlength (arrivals)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (m_pre)) counts )) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_37 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest)) = n_pre)) (PreH29 : ((Zlength (counts)) = n_pre)) (PreH30 : ((Zlength (arrivals)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (m_pre)) counts )) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_38 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest)) = n_pre)) (PreH29 : ((Zlength (counts)) = n_pre)) (PreH30 : ((Zlength (arrivals)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (m_pre)) counts )) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_39 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : ((Zlength (arrivals)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist )) (PreH36 : (Forall (Z.ge (100)) current_dist )) (PreH37 : (Forall (Z.le (0)) latest )) (PreH38 : (Forall (Z.ge (100000)) latest )) (PreH39 : (Forall (Z.le (0)) counts )) (PreH40 : (Forall (Z.ge (m_pre)) counts )) (PreH41 : (Forall (Z.le (0)) arrivals )) (PreH42 : (Forall (Z.ge (200000)) arrivals )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH44 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH45 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((cnt + (Znth j counts 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + (Znth j counts 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : ((Zlength (arrivals)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist )) (PreH36 : (Forall (Z.ge (100)) current_dist )) (PreH37 : (Forall (Z.le (0)) latest )) (PreH38 : (Forall (Z.ge (100000)) latest )) (PreH39 : (Forall (Z.le (0)) counts )) (PreH40 : (Forall (Z.ge (m_pre)) counts )) (PreH41 : (Forall (Z.le (0)) arrivals )) (PreH42 : (Forall (Z.ge (200000)) arrivals )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH44 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH45 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((cnt + (Znth j counts 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + (Znth j counts 0) )) ”
).

Definition solve_safety_wit_39_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : ((Zlength (arrivals)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist )) (PreH36 : (Forall (Z.ge (100)) current_dist )) (PreH37 : (Forall (Z.le (0)) latest )) (PreH38 : (Forall (Z.ge (100000)) latest )) (PreH39 : (Forall (Z.le (0)) counts )) (PreH40 : (Forall (Z.ge (m_pre)) counts )) (PreH41 : (Forall (Z.le (0)) arrivals )) (PreH42 : (Forall (Z.ge (200000)) arrivals )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH44 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH45 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((cnt + (Znth j counts 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_39_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : ((Zlength (arrivals)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist )) (PreH36 : (Forall (Z.ge (100)) current_dist )) (PreH37 : (Forall (Z.le (0)) latest )) (PreH38 : (Forall (Z.ge (100000)) latest )) (PreH39 : (Forall (Z.le (0)) counts )) (PreH40 : (Forall (Z.ge (m_pre)) counts )) (PreH41 : (Forall (Z.le (0)) arrivals )) (PreH42 : (Forall (Z.ge (200000)) arrivals )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH44 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH45 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= (cnt + (Znth j counts 0) )) ”
.

Definition solve_safety_wit_40 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals 0) > (Znth j latest 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : ((Zlength (arrivals)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist )) (PreH37 : (Forall (Z.ge (100)) current_dist )) (PreH38 : (Forall (Z.le (0)) latest )) (PreH39 : (Forall (Z.ge (100000)) latest )) (PreH40 : (Forall (Z.le (0)) counts )) (PreH41 : (Forall (Z.ge (m_pre)) counts )) (PreH42 : (Forall (Z.le (0)) arrivals )) (PreH43 : (Forall (Z.ge (200000)) arrivals )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH45 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH46 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solve_safety_wit_41 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH32 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts latest arrivals i cnt )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_42 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH32 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts latest arrivals i cnt )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_43 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest)) = n_pre)) (PreH29 : ((Zlength (counts)) = n_pre)) (PreH30 : ((Zlength (arrivals)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (m_pre)) counts )) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_44 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 1 ))) (PreH7 : (0 <= best)) (PreH8 : (best <= m_pre)) (PreH9 : ((-1) <= pos)) (PreH10 : (pos < i)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (latest)) = n_pre)) (PreH28 : ((Zlength (counts)) = n_pre)) (PreH29 : ((Zlength (arrivals)) = n_pre)) (PreH30 : (Forall (Z.le (0)) current_dist )) (PreH31 : (Forall (Z.ge (100)) current_dist )) (PreH32 : (Forall (Z.le (0)) latest )) (PreH33 : (Forall (Z.ge (100000)) latest )) (PreH34 : (Forall (Z.le (0)) counts )) (PreH35 : (Forall (Z.ge (m_pre)) counts )) (PreH36 : (Forall (Z.le (0)) arrivals )) (PreH37 : (Forall (Z.ge (200000)) arrivals )) (PreH38 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH39 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_45 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos >= 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest)) = n_pre)) (PreH29 : ((Zlength (counts)) = n_pre)) (PreH30 : ((Zlength (arrivals)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (m_pre)) counts )) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_46 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth pos current_dist 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos current_dist 0) - 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth pos current_dist 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos current_dist 0) - 1 )) ”
).

Definition solve_safety_wit_46_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth pos current_dist 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_46_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((Znth pos current_dist 0) - 1 )) ”
.

Definition solve_safety_wit_47 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_48 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition solve_safety_wit_49 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_50 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i new_arrivals 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i new_arrivals 0) - 1 )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i new_arrivals 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i new_arrivals 0) - 1 )) ”
).

Definition solve_safety_wit_50_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i new_arrivals 0) - 1 ) <= INT_MAX) ”
.

Definition solve_safety_wit_50_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((Znth i new_arrivals 0) - 1 )) ”
.

Definition solve_safety_wit_51 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_52 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) >= (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest)) = n_pre)) (PreH32 : ((Zlength (counts)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (m_pre)) counts )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_safety_wit_53 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition solve_safety_wit_54 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_55 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest)) = n_pre)) (PreH32 : ((Zlength (counts)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (m_pre)) counts )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition solve_safety_wit_56 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest)) = n_pre)) (PreH32 : ((Zlength (counts)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (m_pre)) counts )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_57 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : ((Zlength (arrivals)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (Forall (Z.le (0)) arrivals )) (PreH31 : (Forall (Z.ge (200000)) arrivals )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_58 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest)) = n_pre)) (PreH29 : ((Zlength (counts)) = n_pre)) (PreH30 : ((Zlength (arrivals)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (m_pre)) counts )) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_59 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_60 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : ((Zlength (arrivals)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (Forall (Z.le (0)) arrivals )) (PreH31 : (Forall (Z.ge (200000)) arrivals )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_61 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest)) = n_pre)) (PreH29 : ((Zlength (counts)) = n_pre)) (PreH30 : ((Zlength (arrivals)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (m_pre)) counts )) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_62 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solve_safety_wit_63 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) )) ”
).

Definition solve_safety_wit_63_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_63_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) )) ”
.

Definition solve_safety_wit_64 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) )) ”
).

Definition solve_safety_wit_64_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) <= INT_MAX) ”
.

Definition solve_safety_wit_64_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((INT_MIN) <= (ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) )) ”
.

Definition solve_safety_wit_65 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (((Znth i destinations 0) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i destinations 0) - 1 )) ”
.

Definition solve_safety_wit_66 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solve_safety_wit_67 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ans" ) )) # Int  |-> ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals 0) ) - (Znth i times 0) ))
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solve_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 10000)) (PreH7 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH8 : ((Zlength (times)) = m_pre)) (PreH9 : ((Zlength (origins)) = m_pre)) (PreH10 : ((Zlength (destinations)) = m_pre)) (PreH11 : (Forall (Z.le (0)) dist )) (PreH12 : (Forall (Z.ge (100)) dist )) (PreH13 : (Forall (Z.le (0)) times )) (PreH14 : (Forall (Z.ge (100000)) times )) (PreH15 : (Forall (Z.le (1)) origins )) (PreH16 : (Forall (Z.ge (n_pre)) destinations )) (PreH17 : (Forall2 Z.lt origins destinations )) ,
  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
|--
  EX (counts_prefix: (@list Z))  (latest_prefix: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = 0) ” 
  &&  “ ((Zlength (counts_prefix)) = 0) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix 0 ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg ( &( "late" ) ) 0 0 latest_prefix )
  **  (IntArray.undef_seg ( &( "late" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 0 counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 10000)) (PreH7 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH8 : ((Zlength (times)) = m_pre)) (PreH9 : ((Zlength (origins)) = m_pre)) (PreH10 : ((Zlength (destinations)) = m_pre)) (PreH11 : (Forall (Z.le (0)) dist )) (PreH12 : (Forall (Z.ge (100)) dist )) (PreH13 : (Forall (Z.le (0)) times )) (PreH14 : (Forall (Z.ge (100000)) times )) (PreH15 : (Forall (Z.le (1)) origins )) (PreH16 : (Forall (Z.ge (n_pre)) destinations )) (PreH17 : (Forall2 Z.lt origins destinations )) ,
  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
|--
  “ (WorkspacesZeroPrefix (@nil Z) (@nil Z) 0 ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (IntArray.undef_seg ( &( "late" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
).

Definition solve_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 10000)) (PreH7 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH8 : ((Zlength (times)) = m_pre)) (PreH9 : ((Zlength (origins)) = m_pre)) (PreH10 : ((Zlength (destinations)) = m_pre)) (PreH11 : (Forall (Z.le (0)) dist )) (PreH12 : (Forall (Z.ge (100)) dist )) (PreH13 : (Forall (Z.le (0)) times )) (PreH14 : (Forall (Z.ge (100000)) times )) (PreH15 : (Forall (Z.le (1)) origins )) (PreH16 : (Forall (Z.ge (n_pre)) destinations )) (PreH17 : (Forall2 Z.lt origins destinations )) ,
  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
|--
  “ (WorkspacesZeroPrefix (@nil Z) (@nil Z) 0 ) ”
.

Definition solve_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 10000)) (PreH7 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH8 : ((Zlength (times)) = m_pre)) (PreH9 : ((Zlength (origins)) = m_pre)) (PreH10 : ((Zlength (destinations)) = m_pre)) (PreH11 : (Forall (Z.le (0)) dist )) (PreH12 : (Forall (Z.ge (100)) dist )) (PreH13 : (Forall (Z.le (0)) times )) (PreH14 : (Forall (Z.ge (100000)) times )) (PreH15 : (Forall (Z.le (1)) origins )) (PreH16 : (Forall (Z.ge (n_pre)) destinations )) (PreH17 : (Forall2 Z.lt origins destinations )) ,
  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition solve_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 10000)) (PreH7 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH8 : ((Zlength (times)) = m_pre)) (PreH9 : ((Zlength (origins)) = m_pre)) (PreH10 : ((Zlength (destinations)) = m_pre)) (PreH11 : (Forall (Z.le (0)) dist )) (PreH12 : (Forall (Z.ge (100)) dist )) (PreH13 : (Forall (Z.le (0)) times )) (PreH14 : (Forall (Z.ge (100000)) times )) (PreH15 : (Forall (Z.le (1)) origins )) (PreH16 : (Forall (Z.ge (n_pre)) destinations )) (PreH17 : (Forall2 Z.lt origins destinations )) ,
  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition solve_entail_wit_1_split_goal_spatial := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (PreH1 : (0 <= k_pre)) (PreH2 : (k_pre <= 100000)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 10000)) (PreH7 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH8 : ((Zlength (times)) = m_pre)) (PreH9 : ((Zlength (origins)) = m_pre)) (PreH10 : ((Zlength (destinations)) = m_pre)) (PreH11 : (Forall (Z.le (0)) dist )) (PreH12 : (Forall (Z.ge (100)) dist )) (PreH13 : (Forall (Z.le (0)) times )) (PreH14 : (Forall (Z.ge (100000)) times )) (PreH15 : (Forall (Z.le (1)) origins )) (PreH16 : (Forall (Z.ge (n_pre)) destinations )) (PreH17 : (Forall2 Z.lt origins destinations )) ,
  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
|--
  (IntArray.undef_seg ( &( "late" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (IntArray.seg ( &( "off" ) ) 0 (i + 1 ) (app (counts_prefix_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "off" ) ) (i + 1 ) n_pre )
  **  (IntArray.seg ( &( "late" ) ) 0 (i + 1 ) (app (latest_prefix_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "late" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (counts_prefix: (@list Z))  (latest_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (counts_prefix)) = (i + 1 )) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix (i + 1 ) ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg ( &( "late" ) ) 0 (i + 1 ) latest_prefix )
  **  (IntArray.undef_seg ( &( "late" ) ) (i + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 (i + 1 ) counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) (i + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  TT && emp 
|--
  “ (WorkspacesZeroPrefix (app (latest_prefix_2) ((cons (0) ((@nil Z))))) (app (counts_prefix_2) ((cons (0) ((@nil Z))))) (i + 1 ) ) ” 
  &&  “ ((Zlength ((app (counts_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((Zlength ((app (latest_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solve_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (WorkspacesZeroPrefix (app (latest_prefix_2) ((cons (0) ((@nil Z))))) (app (counts_prefix_2) ((cons (0) ((@nil Z))))) (i + 1 ) )
.

Definition solve_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  ((Zlength ((app (counts_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix_2: (@list Z)) (latest_prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix_2)) = i)) (PreH5 : ((Zlength (counts_prefix_2)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix_2 counts_prefix_2 i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  ((Zlength ((app (latest_prefix_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg ( &( "late" ) ) 0 i latest_prefix )
  **  (IntArray.undef_seg ( &( "late" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (0)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest counts ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (IntArray.seg ( &( "late" ) ) 0 i latest_prefix )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (0)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations 0 latest counts ) ”
  &&  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
).

Definition solve_entail_wit_4 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
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
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) = ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) = ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  ((( &( "x" ) )) # Int  |-> ((Znth (i) (origins) (0)) - 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "y" ) )) # Int  |-> ((Znth (i) (destinations) (0)) - 1 ))
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (0 <= k_pre)) (PreH32 : (k_pre <= 100000)) (PreH33 : ((Zlength (latest)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (i)) counts )) (PreH39 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  TT && emp 
|--
  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (0 <= k_pre)) (PreH32 : (k_pre <= 100000)) (PreH33 : ((Zlength (latest)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (i)) counts )) (PreH39 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (((Znth (i) (destinations) (0)) - 1 ) < n_pre)
.

Definition solve_entail_wit_4_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (0 <= k_pre)) (PreH32 : (k_pre <= 100000)) (PreH33 : ((Zlength (latest)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (i)) counts )) (PreH39 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (0 <= ((Znth (i) (destinations) (0)) - 1 ))
.

Definition solve_entail_wit_4_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (0 <= k_pre)) (PreH32 : (k_pre <= 100000)) (PreH33 : ((Zlength (latest)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (i)) counts )) (PreH39 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (((Znth (i) (origins) (0)) - 1 ) < n_pre)
.

Definition solve_entail_wit_4_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (((Znth i origins 0) - 1 ) <= INT_MAX)) (PreH6 : (((Znth i destinations 0) - 1 ) <= INT_MAX)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (((Znth i origins 0) - 1 ) >= INT_MIN)) (PreH12 : (((Znth i destinations 0) - 1 ) >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (0 <= k_pre)) (PreH32 : (k_pre <= 100000)) (PreH33 : ((Zlength (latest)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (i)) counts )) (PreH39 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (0 <= ((Znth (i) (origins) (0)) - 1 ))
.

Definition solve_entail_wit_5_1 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (IntArray.full ( &( "off" ) ) n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest counts ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  TT && emp 
|--
  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ (Forall (Z.ge (100000)) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)))) = n_pre) ”
  &&  emp
).

Definition solve_entail_wit_5_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_5_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (Forall (Z.ge ((i + 1 ))) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_5_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (Forall (Z.le (0)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_5_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (Forall (Z.ge (100000)) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) )
.

Definition solve_entail_wit_5_1_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (Forall (Z.le (0)) (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)) )
.

Definition solve_entail_wit_5_1_split_goal_6 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre)
.

Definition solve_entail_wit_5_1_split_goal_7 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((Zlength ((replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest_2)))) = n_pre)
.

Definition solve_entail_wit_5_2 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (IntArray.full ( &( "off" ) ) n_pre (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (counts: (@list Z))  (latest: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest counts ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  TT && emp 
|--
  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest_2 (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ (Forall (Z.ge ((i + 1 ))) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre) ”
  &&  emp
).

Definition solve_entail_wit_5_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (PassengerAggregationPrefix n_pre m_pre times origins destinations (i + 1 ) latest_2 (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_5_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (Forall (Z.ge ((i + 1 ))) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_5_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (Forall (Z.le (0)) (replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)) )
.

Definition solve_entail_wit_5_2_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest_2 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (i)) counts_2 )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((Zlength ((replace_Znth (((Znth (i) (destinations) (0)) - 1 )) (((Znth ((Znth (i) (destinations) (0)) - 1 ) counts_2 0) + 1 )) (counts_2)))) = n_pre)
.

Definition solve_entail_wit_6 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest_2 )) (PreH24 : (Forall (Z.ge (100000)) latest_2 )) (PreH25 : (Forall (Z.le (0)) counts_2 )) (PreH26 : (Forall (Z.ge (i)) counts_2 )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix 0 0 ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 0 arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest_2 )) (PreH24 : (Forall (Z.ge (100000)) latest_2 )) (PreH25 : (Forall (Z.le (0)) counts_2 )) (PreH26 : (Forall (Z.ge (i)) counts_2 )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (@nil Z) 0 0 ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts_2 ) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solve_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest_2 )) (PreH24 : (Forall (Z.ge (100000)) latest_2 )) (PreH25 : (Forall (Z.le (0)) counts_2 )) (PreH26 : (Forall (Z.ge (i)) counts_2 )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (@nil Z) 0 0 )
.

Definition solve_entail_wit_6_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest_2 )) (PreH24 : (Forall (Z.ge (100000)) latest_2 )) (PreH25 : (Forall (Z.le (0)) counts_2 )) (PreH26 : (Forall (Z.ge (i)) counts_2 )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (Forall (Z.ge (m_pre)) counts_2 )
.

Definition solve_entail_wit_6_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest_2 )) (PreH24 : (Forall (Z.ge (100000)) latest_2 )) (PreH25 : (Forall (Z.le (0)) counts_2 )) (PreH26 : (Forall (Z.ge (i)) counts_2 )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )
.

Definition solve_entail_wit_6_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest_2 )) (PreH24 : (Forall (Z.ge (100000)) latest_2 )) (PreH25 : (Forall (Z.le (0)) counts_2 )) (PreH26 : (Forall (Z.ge (i)) counts_2 )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest_2 counts_2 )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solve_entail_wit_7_1 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((Znth i latest_2 0) + (Znth i dist 0) )) ” 
  &&  “ (((Znth i latest_2 0) + (Znth i dist 0) ) <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) ((Znth i latest_2 0) + (Znth i dist 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) ((Znth i latest_2 0) + (Znth i dist 0) ) ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (((Znth i latest_2 0) + (Znth i dist 0) ) <= 200000) ” 
  &&  “ (0 <= ((Znth i latest_2 0) + (Znth i dist 0) )) ”
  &&  emp
).

Definition solve_entail_wit_7_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) ((Znth i latest_2 0) + (Znth i dist 0) ) )
.

Definition solve_entail_wit_7_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_7_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (((Znth i latest_2 0) + (Znth i dist 0) ) <= 200000)
.

Definition solve_entail_wit_7_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (0 <= ((Znth i latest_2 0) + (Znth i dist 0) ))
.

Definition solve_entail_wit_7_2 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (cur + (Znth i dist 0) )) ” 
  &&  “ ((cur + (Znth i dist 0) ) <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) (cur + (Znth i dist 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (cur + (Znth i dist 0) ) ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((cur + (Znth i dist 0) ) <= 200000) ” 
  &&  “ (0 <= (cur + (Znth i dist 0) )) ”
  &&  emp
).

Definition solve_entail_wit_7_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (cur + (Znth i dist 0) ) )
.

Definition solve_entail_wit_7_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_7_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((cur + (Znth i dist 0) ) <= 200000)
.

Definition solve_entail_wit_7_2_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (0 <= (cur + (Znth i dist 0) ))
.

Definition solve_entail_wit_7_3 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (Znth i latest_2 0)) ” 
  &&  “ ((Znth i latest_2 0) <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) (Znth i latest_2 0) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (Znth i latest_2 0) ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((Znth i latest_2 0) <= 200000) ”
  &&  emp
).

Definition solve_entail_wit_7_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) (Znth i latest_2 0) )
.

Definition solve_entail_wit_7_3_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_7_3_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur < (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Znth i latest_2 0) <= 200000)
.

Definition solve_entail_wit_7_4 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (latest: (@list Z))  (counts: (@list Z))  (arrivals_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = (i + 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix (i + 1 ) cur ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  TT && emp 
|--
  “ (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) cur ) ” 
  &&  “ ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solve_entail_wit_7_4_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  (ArrivalSimulationPrefix n_pre dist latest_2 (app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))) (i + 1 ) cur )
.

Definition solve_entail_wit_7_4_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix_2: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) >= n_pre)) (PreH2 : (cur >= (Znth i latest_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix_2)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH27 : (Forall (Z.le (0)) latest_2 )) (PreH28 : (Forall (Z.ge (100000)) latest_2 )) (PreH29 : (Forall (Z.le (0)) counts_2 )) (PreH30 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix_2 i cur )) ,
  ((Zlength ((app (arrivals_prefix_2) ((cons (cur) ((@nil Z))))))) = (i + 1 ))
.

Definition solve_entail_wit_8 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) (PreH24 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH25 : (Forall (Z.le (0)) latest_2 )) (PreH26 : (Forall (Z.ge (100000)) latest_2 )) (PreH27 : (Forall (Z.le (0)) counts_2 )) (PreH28 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH29 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix i cur )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 i arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k_pre dist times origins destinations current_dist latest counts arrivals ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) (PreH24 : (StationSummaryState n_pre m_pre times origins destinations latest_2 counts_2 )) (PreH25 : (Forall (Z.le (0)) latest_2 )) (PreH26 : (Forall (Z.ge (100000)) latest_2 )) (PreH27 : (Forall (Z.le (0)) counts_2 )) (PreH28 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH29 : (ArrivalSimulationPrefix n_pre dist latest_2 arrivals_prefix i cur )) ,
  (IntArray.seg ( &( "arr" ) ) 0 i arrivals_prefix )
|--
  EX (arrivals: (@list Z)) ,
  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest_2)) = n_pre) ” 
  &&  “ ((Zlength (counts_2)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) latest_2 ) ” 
  &&  “ (Forall (Z.ge (100000)) latest_2 ) ” 
  &&  “ (Forall (Z.le (0)) counts_2 ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts_2 ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k_pre dist times origins destinations dist latest_2 counts_2 arrivals ) ”
  &&  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
).

Definition solve_entail_wit_9 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist_2 )) (PreH25 : (Forall (Z.ge (100)) current_dist_2 )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals 0 0 (-1) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist_2 )) (PreH25 : (Forall (Z.ge (100)) current_dist_2 )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 0 0 (-1) ) ”
  &&  emp
).

Definition solve_entail_wit_9_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (k: Z) (PreH1 : (k > 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist_2 )) (PreH25 : (Forall (Z.ge (100)) current_dist_2 )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 0 0 (-1) )
.

Definition solve_entail_wit_10 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist_2 )) (PreH32 : (Forall (Z.ge (100)) current_dist_2 )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i (i + 1 ) 0 ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist_2 )) (PreH32 : (Forall (Z.ge (100)) current_dist_2 )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (i + 1 ) 0 ) ”
  &&  emp
).

Definition solve_entail_wit_10_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) > 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist_2 )) (PreH32 : (Forall (Z.ge (100)) current_dist_2 )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (i + 1 ) 0 )
.

Definition solve_entail_wit_11 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts_2)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts_2 )) (PreH41 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i (j + 1 ) (cnt + (Znth j counts_2 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts_2)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts_2 )) (PreH41 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  TT && emp 
|--
  “ (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (j + 1 ) (cnt + (Znth j counts_2 0) ) ) ” 
  &&  “ ((cnt + (Znth j counts_2 0) ) <= m_pre) ” 
  &&  “ (0 <= (cnt + (Znth j counts_2 0) )) ”
  &&  emp
).

Definition solve_entail_wit_11_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts_2)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts_2 )) (PreH41 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (MarginalBenefitScan counts_2 latest_2 arrivals_2 i (j + 1 ) (cnt + (Znth j counts_2 0) ) )
.

Definition solve_entail_wit_11_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts_2)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts_2 )) (PreH41 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  ((cnt + (Znth j counts_2 0) ) <= m_pre)
.

Definition solve_entail_wit_11_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) > (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts_2)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts_2 )) (PreH41 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (0 <= (cnt + (Znth j counts_2 0) ))
.

Definition solve_entail_wit_12_1 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : ((Zlength (arrivals_2)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist_2 )) (PreH36 : (Forall (Z.ge (100)) current_dist_2 )) (PreH37 : (Forall (Z.le (0)) latest_2 )) (PreH38 : (Forall (Z.ge (100000)) latest_2 )) (PreH39 : (Forall (Z.le (0)) counts_2 )) (PreH40 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH41 : (Forall (Z.le (0)) arrivals_2 )) (PreH42 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH44 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH45 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (EdgeMarginalBenefit n_pre counts latest arrivals i cnt ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : ((Zlength (arrivals_2)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist_2 )) (PreH36 : (Forall (Z.ge (100)) current_dist_2 )) (PreH37 : (Forall (Z.le (0)) latest_2 )) (PreH38 : (Forall (Z.ge (100000)) latest_2 )) (PreH39 : (Forall (Z.le (0)) counts_2 )) (PreH40 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH41 : (Forall (Z.le (0)) arrivals_2 )) (PreH42 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH44 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH45 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  TT && emp 
|--
  “ (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt ) ”
  &&  emp
).

Definition solve_entail_wit_12_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest_2)) = n_pre)) (PreH33 : ((Zlength (counts_2)) = n_pre)) (PreH34 : ((Zlength (arrivals_2)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist_2 )) (PreH36 : (Forall (Z.ge (100)) current_dist_2 )) (PreH37 : (Forall (Z.le (0)) latest_2 )) (PreH38 : (Forall (Z.ge (100000)) latest_2 )) (PreH39 : (Forall (Z.le (0)) counts_2 )) (PreH40 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH41 : (Forall (Z.le (0)) arrivals_2 )) (PreH42 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH44 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH45 : (MarginalBenefitScan counts_2 latest_2 arrivals_2 i j cnt )) ,
  (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )
.

Definition solve_entail_wit_12_2 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts )) (PreH41 : (Forall (Z.ge (m_pre)) counts )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts_2 arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts_2 latest arrivals i best pos ) ” 
  &&  “ (EdgeMarginalBenefit n_pre counts_2 latest arrivals i (cnt + (Znth j counts 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts )) (PreH41 : (Forall (Z.ge (m_pre)) counts )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  TT && emp 
|--
  “ (EdgeMarginalBenefit n_pre counts latest_2 arrivals_2 i (cnt + (Znth j counts 0) ) ) ” 
  &&  “ ((cnt + (Znth j counts 0) ) <= m_pre) ” 
  &&  “ (0 <= (cnt + (Znth j counts 0) )) ”
  &&  emp
).

Definition solve_entail_wit_12_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts )) (PreH41 : (Forall (Z.ge (m_pre)) counts )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  (EdgeMarginalBenefit n_pre counts latest_2 arrivals_2 i (cnt + (Znth j counts 0) ) )
.

Definition solve_entail_wit_12_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts )) (PreH41 : (Forall (Z.ge (m_pre)) counts )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  ((cnt + (Znth j counts 0) ) <= m_pre)
.

Definition solve_entail_wit_12_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : ((Znth j arrivals_2 0) <= (Znth j latest_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i < (n_pre - 1 ))) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt <= m_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= m_pre)) (PreH14 : ((-1) <= pos)) (PreH15 : (pos < i)) (PreH16 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : (1 <= m_pre)) (PreH20 : (m_pre <= 10000)) (PreH21 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH22 : ((Zlength (times)) = m_pre)) (PreH23 : ((Zlength (origins)) = m_pre)) (PreH24 : ((Zlength (destinations)) = m_pre)) (PreH25 : (Forall (Z.le (0)) dist )) (PreH26 : (Forall (Z.ge (100)) dist )) (PreH27 : (Forall (Z.le (0)) times )) (PreH28 : (Forall (Z.ge (100000)) times )) (PreH29 : (Forall (Z.le (1)) origins )) (PreH30 : (Forall (Z.ge (n_pre)) destinations )) (PreH31 : (Forall2 Z.lt origins destinations )) (PreH32 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH33 : ((Zlength (latest_2)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : ((Zlength (arrivals_2)) = n_pre)) (PreH36 : (Forall (Z.le (0)) current_dist_2 )) (PreH37 : (Forall (Z.ge (100)) current_dist_2 )) (PreH38 : (Forall (Z.le (0)) latest_2 )) (PreH39 : (Forall (Z.ge (100000)) latest_2 )) (PreH40 : (Forall (Z.le (0)) counts )) (PreH41 : (Forall (Z.ge (m_pre)) counts )) (PreH42 : (Forall (Z.le (0)) arrivals_2 )) (PreH43 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH44 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts arrivals_2 )) (PreH45 : (EdgeChoicePrefix n_pre current_dist_2 counts latest_2 arrivals_2 i best pos )) (PreH46 : (MarginalBenefitScan counts latest_2 arrivals_2 i j cnt )) ,
  (0 <= (cnt + (Znth j counts 0) ))
.

Definition solve_entail_wit_13_1 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals (i + 1 ) cnt i ) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) cnt i ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals_2 ) ” 
  &&  “ (Forall (Z.le (0)) arrivals_2 ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts_2 ) ” 
  &&  “ (Forall (Z.le (0)) counts_2 ) ” 
  &&  “ (Forall (Z.ge (100000)) latest_2 ) ” 
  &&  “ (Forall (Z.le (0)) latest_2 ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist_2 ) ” 
  &&  “ (Forall (Z.le (0)) current_dist_2 ) ” 
  &&  “ ((Zlength (arrivals_2)) = n_pre) ” 
  &&  “ ((Zlength (counts_2)) = n_pre) ” 
  &&  “ ((Zlength (latest_2)) = n_pre) ” 
  &&  “ ((Zlength (current_dist_2)) = (n_pre - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_13_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) cnt i )
.

Definition solve_entail_wit_13_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (200000)) arrivals_2 )
.

Definition solve_entail_wit_13_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) arrivals_2 )
.

Definition solve_entail_wit_13_1_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (m_pre)) counts_2 )
.

Definition solve_entail_wit_13_1_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) counts_2 )
.

Definition solve_entail_wit_13_1_split_goal_6 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (100000)) latest_2 )
.

Definition solve_entail_wit_13_1_split_goal_7 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) latest_2 )
.

Definition solve_entail_wit_13_1_split_goal_8 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (100)) current_dist_2 )
.

Definition solve_entail_wit_13_1_split_goal_9 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) current_dist_2 )
.

Definition solve_entail_wit_13_1_split_goal_10 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (arrivals_2)) = n_pre)
.

Definition solve_entail_wit_13_1_split_goal_11 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (counts_2)) = n_pre)
.

Definition solve_entail_wit_13_1_split_goal_12 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (latest_2)) = n_pre)
.

Definition solve_entail_wit_13_1_split_goal_13 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best < cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (current_dist_2)) = (n_pre - 1 ))
.

Definition solve_entail_wit_13_2 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals (i + 1 ) best pos ) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals_2 ) ” 
  &&  “ (Forall (Z.le (0)) arrivals_2 ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts_2 ) ” 
  &&  “ (Forall (Z.le (0)) counts_2 ) ” 
  &&  “ (Forall (Z.ge (100000)) latest_2 ) ” 
  &&  “ (Forall (Z.le (0)) latest_2 ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist_2 ) ” 
  &&  “ (Forall (Z.le (0)) current_dist_2 ) ” 
  &&  “ ((Zlength (arrivals_2)) = n_pre) ” 
  &&  “ ((Zlength (counts_2)) = n_pre) ” 
  &&  “ ((Zlength (latest_2)) = n_pre) ” 
  &&  “ ((Zlength (current_dist_2)) = (n_pre - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_13_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos )
.

Definition solve_entail_wit_13_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (200000)) arrivals_2 )
.

Definition solve_entail_wit_13_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) arrivals_2 )
.

Definition solve_entail_wit_13_2_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (m_pre)) counts_2 )
.

Definition solve_entail_wit_13_2_split_goal_5 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) counts_2 )
.

Definition solve_entail_wit_13_2_split_goal_6 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (100000)) latest_2 )
.

Definition solve_entail_wit_13_2_split_goal_7 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) latest_2 )
.

Definition solve_entail_wit_13_2_split_goal_8 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.ge (100)) current_dist_2 )
.

Definition solve_entail_wit_13_2_split_goal_9 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  (Forall (Z.le (0)) current_dist_2 )
.

Definition solve_entail_wit_13_2_split_goal_10 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (arrivals_2)) = n_pre)
.

Definition solve_entail_wit_13_2_split_goal_11 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (counts_2)) = n_pre)
.

Definition solve_entail_wit_13_2_split_goal_12 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (latest_2)) = n_pre)
.

Definition solve_entail_wit_13_2_split_goal_13 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (current_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (k: Z) (i: Z) (cnt: Z) (best: Z) (pos: Z) (j: Z) (PreH1 : (best >= cnt)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : (0 <= cnt)) (PreH8 : (cnt <= m_pre)) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 < (Znth (i) (current_dist_2) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH32 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) (PreH33 : (EdgeMarginalBenefit n_pre counts_2 latest_2 arrivals_2 i cnt )) ,
  ((Zlength (current_dist_2)) = (n_pre - 1 ))
.

Definition solve_entail_wit_13_3 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist_2 )) (PreH32 : (Forall (Z.ge (100)) current_dist_2 )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals (i + 1 ) best pos ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist_2 )) (PreH32 : (Forall (Z.ge (100)) current_dist_2 )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos ) ”
  &&  emp
).

Definition solve_entail_wit_13_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist_2: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((Znth i current_dist_2 0) <= 0)) (PreH2 : ((i + 1 ) < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist_2 )) (PreH32 : (Forall (Z.ge (100)) current_dist_2 )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist_2 latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 i best pos )) ,
  (EdgeChoicePrefix n_pre current_dist_2 counts_2 latest_2 arrivals_2 (i + 1 ) best pos )
.

Definition solve_entail_wit_14 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest_2)) = n_pre)) (PreH30 : ((Zlength (counts_2)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) new_dist ) ” 
  &&  “ (Forall (Z.ge (100)) new_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) new_arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) new_arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos (pos + 1 ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest_2)) = n_pre)) (PreH30 : ((Zlength (counts_2)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals i best pos )) ,
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
  &&  “ (Forall (Z.le (0)) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) ) ” 
  &&  “ (Forall (Z.ge (100)) (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) ) ” 
  &&  “ (BoosterProgress (Zlength (latest_2)) (Zlength (times)) k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals ) ” 
  &&  “ (BestBoostChoice (Zlength (latest_2)) old_dist counts_2 latest_2 old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress (Zlength (latest_2)) old_dist old_arrivals (replace_Znth (pos) (((Znth pos current_dist 0) - 1 )) (current_dist)) arrivals latest_2 pos (pos + 1 ) ) ”
  &&  emp
).

Definition solve_entail_wit_15 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) 0) >= (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH30 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist_2 )) (PreH34 : (Forall (Z.ge (100)) new_dist_2 )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals_2 )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals_2 )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH42 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) new_dist ) ” 
  &&  “ (Forall (Z.ge (100)) new_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) new_arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) new_arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos (i + 1 ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals_2: (@list Z)) (old_arrivals_2: (@list Z)) (new_dist_2: (@list Z)) (old_dist_2: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) 0) >= (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist_2)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist_2)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals_2)) = n_pre)) (PreH30 : ((Zlength (new_arrivals_2)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist_2 )) (PreH34 : (Forall (Z.ge (100)) new_dist_2 )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals_2 )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals_2 )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist_2 latest_2 counts_2 old_arrivals_2 )) (PreH42 : (BestBoostChoice n_pre old_dist_2 counts_2 latest_2 old_arrivals_2 best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2 new_arrivals_2 latest_2 pos i )) ,
  TT && emp 
|--
  EX (old_arrivals: (@list Z))  (old_dist: (@list Z)) ,
  “ ((pos + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (old_arrivals_2))) ” 
  &&  “ ((Zlength (old_dist)) = ((Zlength (old_arrivals_2)) - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = (Zlength (old_arrivals_2))) ” 
  &&  “ ((Zlength ((replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)))) = (Zlength (old_arrivals_2))) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) ) ” 
  &&  “ (Forall (Z.ge (200000)) (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) ) ” 
  &&  “ (BoosterProgress (Zlength (old_arrivals_2)) (Zlength (times)) k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals ) ” 
  &&  “ (BestBoostChoice (Zlength (old_arrivals_2)) old_dist counts_2 latest_2 old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress (Zlength (old_arrivals_2)) old_dist old_arrivals new_dist_2 (replace_Znth (i) (((Znth i new_arrivals_2 0) - 1 )) (new_arrivals_2)) latest_2 pos (i + 1 ) ) ”
  &&  emp
).

Definition solve_entail_wit_16_1 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest_2)) = n_pre)) (PreH31 : ((Zlength (counts_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations current_dist latest counts arrivals ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest_2)) = n_pre)) (PreH31 : ((Zlength (counts_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  TT && emp 
|--
  “ (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations new_dist latest_2 counts_2 new_arrivals ) ”
  &&  emp
).

Definition solve_entail_wit_16_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest_2)) = n_pre)) (PreH31 : ((Zlength (counts_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations new_dist latest_2 counts_2 new_arrivals )
.

Definition solve_entail_wit_16_2 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (arrivals: (@list Z))  (counts: (@list Z))  (latest: (@list Z))  (current_dist: (@list Z)) ,
  “ (0 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations current_dist latest counts arrivals ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  TT && emp 
|--
  “ (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations new_dist latest_2 counts_2 (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) ) ” 
  &&  “ (Forall (Z.ge (200000)) (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) ) ” 
  &&  “ ((Zlength ((replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)))) = n_pre) ”
  &&  emp
).

Definition solve_entail_wit_16_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  (BoosterProgress n_pre m_pre k_pre (k - 1 ) dist times origins destinations new_dist latest_2 counts_2 (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
.

Definition solve_entail_wit_16_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  (Forall (Z.ge (200000)) (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
.

Definition solve_entail_wit_16_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  (Forall (Z.le (0)) (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
.

Definition solve_entail_wit_16_2_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : ((Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0) < (Znth i latest_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= pos)) (PreH7 : (pos < (n_pre - 1 ))) (PreH8 : (0 < best)) (PreH9 : (best <= m_pre)) (PreH10 : ((pos + 1 ) <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (old_arrivals)) = n_pre)) (PreH30 : ((Zlength (new_arrivals)) = n_pre)) (PreH31 : ((Zlength (latest_2)) = n_pre)) (PreH32 : ((Zlength (counts_2)) = n_pre)) (PreH33 : (Forall (Z.le (0)) new_dist )) (PreH34 : (Forall (Z.ge (100)) new_dist )) (PreH35 : (Forall (Z.le (0)) latest_2 )) (PreH36 : (Forall (Z.ge (100000)) latest_2 )) (PreH37 : (Forall (Z.le (0)) counts_2 )) (PreH38 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH39 : (Forall (Z.le (0)) new_arrivals )) (PreH40 : (Forall (Z.ge (200000)) new_arrivals )) (PreH41 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals )) (PreH42 : (BestBoostChoice n_pre old_dist counts_2 latest_2 old_arrivals best pos )) (PreH43 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest_2 pos i )) ,
  ((Zlength ((replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)))) = n_pre)
.

Definition solve_entail_wit_17_1 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals 0 0 ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 0 0 ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 ) ”
  &&  emp
).

Definition solve_entail_wit_17_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 0 0 )
.

Definition solve_entail_wit_17_1_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (Forall (Z.le (1)) destinations )
.

Definition solve_entail_wit_17_1_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (k: Z) (PreH1 : (k <= 0)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 10000)) (PreH9 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH10 : ((Zlength (times)) = m_pre)) (PreH11 : ((Zlength (origins)) = m_pre)) (PreH12 : ((Zlength (destinations)) = m_pre)) (PreH13 : (Forall (Z.le (0)) dist )) (PreH14 : (Forall (Z.ge (100)) dist )) (PreH15 : (Forall (Z.le (0)) times )) (PreH16 : (Forall (Z.ge (100000)) times )) (PreH17 : (Forall (Z.le (1)) origins )) (PreH18 : (Forall (Z.ge (n_pre)) destinations )) (PreH19 : (Forall2 Z.lt origins destinations )) (PreH20 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (latest_2)) = n_pre)) (PreH22 : ((Zlength (counts_2)) = n_pre)) (PreH23 : ((Zlength (arrivals_2)) = n_pre)) (PreH24 : (Forall (Z.le (0)) current_dist )) (PreH25 : (Forall (Z.ge (100)) current_dist )) (PreH26 : (Forall (Z.le (0)) latest_2 )) (PreH27 : (Forall (Z.ge (100000)) latest_2 )) (PreH28 : (Forall (Z.le (0)) counts_2 )) (PreH29 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH30 : (Forall (Z.le (0)) arrivals_2 )) (PreH31 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH32 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) ,
  (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )
.

Definition solve_entail_wit_17_2 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals 0 0 ) ”
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 0 0 ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 ) ”
  &&  emp
).

Definition solve_entail_wit_17_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 0 0 )
.

Definition solve_entail_wit_17_2_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (Forall (Z.le (1)) destinations )
.

Definition solve_entail_wit_17_2_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (pos < 0)) (PreH2 : ((i + 1 ) >= n_pre)) (PreH3 : (0 < k)) (PreH4 : (k <= k_pre)) (PreH5 : (k_pre <= 100000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 1 ))) (PreH8 : (0 <= best)) (PreH9 : (best <= m_pre)) (PreH10 : ((-1) <= pos)) (PreH11 : (pos < i)) (PreH12 : (2 <= n_pre)) (PreH13 : (n_pre <= 1000)) (PreH14 : (1 <= m_pre)) (PreH15 : (m_pre <= 10000)) (PreH16 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH17 : ((Zlength (times)) = m_pre)) (PreH18 : ((Zlength (origins)) = m_pre)) (PreH19 : ((Zlength (destinations)) = m_pre)) (PreH20 : (Forall (Z.le (0)) dist )) (PreH21 : (Forall (Z.ge (100)) dist )) (PreH22 : (Forall (Z.le (0)) times )) (PreH23 : (Forall (Z.ge (100000)) times )) (PreH24 : (Forall (Z.le (1)) origins )) (PreH25 : (Forall (Z.ge (n_pre)) destinations )) (PreH26 : (Forall2 Z.lt origins destinations )) (PreH27 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (latest_2)) = n_pre)) (PreH29 : ((Zlength (counts_2)) = n_pre)) (PreH30 : ((Zlength (arrivals_2)) = n_pre)) (PreH31 : (Forall (Z.le (0)) current_dist )) (PreH32 : (Forall (Z.ge (100)) current_dist )) (PreH33 : (Forall (Z.le (0)) latest_2 )) (PreH34 : (Forall (Z.ge (100000)) latest_2 )) (PreH35 : (Forall (Z.le (0)) counts_2 )) (PreH36 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH40 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )
.

Definition solve_entail_wit_17_3 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest_2)) = n_pre)) (PreH30 : ((Zlength (counts_2)) = n_pre)) (PreH31 : ((Zlength (arrivals_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) arrivals_2 )) (PreH39 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals 0 0 ) ”
  &&  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest_2)) = n_pre)) (PreH30 : ((Zlength (counts_2)) = n_pre)) (PreH31 : ((Zlength (arrivals_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) arrivals_2 )) (PreH39 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 0 0 ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 ) ”
  &&  emp
).

Definition solve_entail_wit_17_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest_2)) = n_pre)) (PreH30 : ((Zlength (counts_2)) = n_pre)) (PreH31 : ((Zlength (arrivals_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) arrivals_2 )) (PreH39 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 0 0 )
.

Definition solve_entail_wit_17_3_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest_2)) = n_pre)) (PreH30 : ((Zlength (counts_2)) = n_pre)) (PreH31 : ((Zlength (arrivals_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) arrivals_2 )) (PreH39 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (Forall (Z.le (1)) destinations )
.

Definition solve_entail_wit_17_3_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals_2: (@list Z)) (counts_2: (@list Z)) (latest_2: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best = 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest_2)) = n_pre)) (PreH30 : ((Zlength (counts_2)) = n_pre)) (PreH31 : ((Zlength (arrivals_2)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest_2 )) (PreH35 : (Forall (Z.ge (100000)) latest_2 )) (PreH36 : (Forall (Z.le (0)) counts_2 )) (PreH37 : (Forall (Z.ge (m_pre)) counts_2 )) (PreH38 : (Forall (Z.le (0)) arrivals_2 )) (PreH39 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts_2 latest_2 arrivals_2 i best pos )) ,
  (OptimizedBusState n_pre m_pre k_pre dist times origins destinations current_dist latest_2 counts_2 arrivals_2 )
.

Definition solve_entail_wit_18 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 10000)) (PreH14 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (times)) = m_pre)) (PreH16 : ((Zlength (origins)) = m_pre)) (PreH17 : ((Zlength (destinations)) = m_pre)) (PreH18 : (Forall (Z.le (0)) dist )) (PreH19 : (Forall (Z.ge (100)) dist )) (PreH20 : (Forall (Z.le (0)) times )) (PreH21 : (Forall (Z.ge (100000)) times )) (PreH22 : (Forall (Z.le (1)) origins )) (PreH23 : (Forall (Z.ge (n_pre)) destinations )) (PreH24 : (Forall2 Z.lt origins destinations )) (PreH25 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH26 : ((Zlength (arrivals)) = n_pre)) (PreH27 : (Forall (Z.le (0)) arrivals )) (PreH28 : (Forall (Z.ge (200000)) arrivals )) (PreH29 : (Forall (Z.le (1)) destinations )) (PreH30 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
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
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (k <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  TT && emp 
|--
  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ”
  &&  emp
).

Definition solve_entail_wit_18_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (k <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (((Znth (i) (destinations) (0)) - 1 ) < n_pre)
.

Definition solve_entail_wit_18_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (ans <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (k <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (0 <= ((Znth (i) (destinations) (0)) - 1 ))
.

Definition solve_entail_wit_19 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH36 : ((Zlength (arrivals_2)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals_2 )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist_2 )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest_2 )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts_2 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals (i + 1 ) ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH36 : ((Zlength (arrivals_2)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  TT && emp 
|--
  “ (TravelSumPrefix m_pre times destinations arrivals_2 (i + 1 ) ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) ) ” 
  &&  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= 2000000000) ” 
  &&  “ (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= ((i + 1 ) * 200000 )) ” 
  &&  “ (0 <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) )) ”
  &&  emp
).

Definition solve_entail_wit_19_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH36 : ((Zlength (arrivals_2)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (TravelSumPrefix m_pre times destinations arrivals_2 (i + 1 ) ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) )
.

Definition solve_entail_wit_19_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH36 : ((Zlength (arrivals_2)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= 2000000000)
.

Definition solve_entail_wit_19_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH36 : ((Zlength (arrivals_2)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ) <= ((i + 1 ) * 200000 ))
.

Definition solve_entail_wit_19_split_goal_4 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest_2: (@list Z)) (counts_2: (@list Z)) (arrivals_2: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest_2 counts_2 arrivals_2 )) (PreH36 : ((Zlength (arrivals_2)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals_2 )) (PreH38 : (Forall (Z.ge (200000)) arrivals_2 )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals_2 i ans )) ,
  (0 <= ((ans + (Znth ((Znth i destinations 0) - 1 ) arrivals_2 0) ) - (Znth i times 0) ))
.

Definition solve_entail_wit_20 := 
(
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 10000)) (PreH14 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (times)) = m_pre)) (PreH16 : ((Zlength (origins)) = m_pre)) (PreH17 : ((Zlength (destinations)) = m_pre)) (PreH18 : (Forall (Z.le (0)) dist )) (PreH19 : (Forall (Z.ge (100)) dist )) (PreH20 : (Forall (Z.le (0)) times )) (PreH21 : (Forall (Z.ge (100000)) times )) (PreH22 : (Forall (Z.le (1)) origins )) (PreH23 : (Forall (Z.ge (n_pre)) destinations )) (PreH24 : (Forall2 Z.lt origins destinations )) (PreH25 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest counts arrivals )) (PreH26 : ((Zlength (arrivals)) = n_pre)) (PreH27 : (Forall (Z.le (0)) arrivals )) (PreH28 : (Forall (Z.ge (200000)) arrivals )) (PreH29 : (Forall (Z.le (1)) destinations )) (PreH30 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  EX (final_dist: (@list Z)) ,
  “ (SightseeingMinimumTotal n_pre m_pre k_pre dist times origins destinations ans ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_full ( &( "late" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) 1000 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |->_)
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 10000)) (PreH14 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (times)) = m_pre)) (PreH16 : ((Zlength (origins)) = m_pre)) (PreH17 : ((Zlength (destinations)) = m_pre)) (PreH18 : (Forall (Z.le (0)) dist )) (PreH19 : (Forall (Z.ge (100)) dist )) (PreH20 : (Forall (Z.le (0)) times )) (PreH21 : (Forall (Z.ge (100000)) times )) (PreH22 : (Forall (Z.le (1)) origins )) (PreH23 : (Forall (Z.ge (n_pre)) destinations )) (PreH24 : (Forall2 Z.lt origins destinations )) (PreH25 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest counts arrivals )) (PreH26 : ((Zlength (arrivals)) = n_pre)) (PreH27 : (Forall (Z.le (0)) arrivals )) (PreH28 : (Forall (Z.ge (200000)) arrivals )) (PreH29 : (Forall (Z.le (1)) destinations )) (PreH30 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (SightseeingMinimumTotal n_pre m_pre k_pre dist times origins destinations ans ) ”
  &&  (IntArray.undef_full ( &( "late" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) 1000 )
).

Definition solve_entail_wit_20_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 10000)) (PreH14 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (times)) = m_pre)) (PreH16 : ((Zlength (origins)) = m_pre)) (PreH17 : ((Zlength (destinations)) = m_pre)) (PreH18 : (Forall (Z.le (0)) dist )) (PreH19 : (Forall (Z.ge (100)) dist )) (PreH20 : (Forall (Z.le (0)) times )) (PreH21 : (Forall (Z.ge (100000)) times )) (PreH22 : (Forall (Z.le (1)) origins )) (PreH23 : (Forall (Z.ge (n_pre)) destinations )) (PreH24 : (Forall2 Z.lt origins destinations )) (PreH25 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest counts arrivals )) (PreH26 : ((Zlength (arrivals)) = n_pre)) (PreH27 : (Forall (Z.le (0)) arrivals )) (PreH28 : (Forall (Z.ge (200000)) arrivals )) (PreH29 : (Forall (Z.le (1)) destinations )) (PreH30 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (SightseeingMinimumTotal n_pre m_pre k_pre dist times origins destinations ans ) ”
.

Definition solve_entail_wit_20_split_goal_spatial := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= m_pre)) (PreH7 : (0 <= ans)) (PreH8 : (ans <= (i * 200000 ))) (PreH9 : (ans <= 2000000000)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 1000)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre <= 10000)) (PreH14 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH15 : ((Zlength (times)) = m_pre)) (PreH16 : ((Zlength (origins)) = m_pre)) (PreH17 : ((Zlength (destinations)) = m_pre)) (PreH18 : (Forall (Z.le (0)) dist )) (PreH19 : (Forall (Z.ge (100)) dist )) (PreH20 : (Forall (Z.le (0)) times )) (PreH21 : (Forall (Z.ge (100000)) times )) (PreH22 : (Forall (Z.le (1)) origins )) (PreH23 : (Forall (Z.ge (n_pre)) destinations )) (PreH24 : (Forall2 Z.lt origins destinations )) (PreH25 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist_2 latest counts arrivals )) (PreH26 : ((Zlength (arrivals)) = n_pre)) (PreH27 : (Forall (Z.le (0)) arrivals )) (PreH28 : (Forall (Z.ge (200000)) arrivals )) (PreH29 : (Forall (Z.le (1)) destinations )) (PreH30 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  (IntArray.undef_full ( &( "late" ) ) 1000 )
  **  (IntArray.undef_full ( &( "off" ) ) 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) 1000 )
.

Definition solve_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist_2: (@list Z)) (ans: Z) (PreH1 : (SightseeingMinimumTotal n_pre m_pre k_pre dist times origins destinations ans )) ,
  (IntArray.full d_pre (n_pre - 1 ) final_dist_2 )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
|--
  EX (final_dist: (@list Z)) ,
  “ (SightseeingMinimumTotal n_pre m_pre k_pre dist times origins destinations ans ) ”
  &&  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
.

Definition solve_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg ( &( "late" ) ) 0 i latest_prefix )
  **  (IntArray.undef_seg ( &( "late" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = i) ” 
  &&  “ ((Zlength (counts_prefix)) = i) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix i ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (((( &( "late" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "late" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.seg ( &( "late" ) ) 0 i latest_prefix )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts_prefix: (@list Z)) (latest_prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((Zlength (latest_prefix)) = i)) (PreH5 : ((Zlength (counts_prefix)) = i)) (PreH6 : (WorkspacesZeroPrefix latest_prefix counts_prefix i )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) ,
  (IntArray.seg ( &( "late" ) ) 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "late" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (latest_prefix)) = i) ” 
  &&  “ ((Zlength (counts_prefix)) = i) ” 
  &&  “ (WorkspacesZeroPrefix latest_prefix counts_prefix i ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ”
  &&  (((( &( "off" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "off" ) ) (i + 1 ) n_pre )
  **  (IntArray.seg ( &( "late" ) ) 0 (i + 1 ) (app (latest_prefix) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "late" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "off" ) ) 0 i counts_prefix )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i origins 0))
  **  (IntArray.missing_i a_pre i 0 m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 10000)) (PreH8 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH9 : ((Zlength (times)) = m_pre)) (PreH10 : ((Zlength (origins)) = m_pre)) (PreH11 : ((Zlength (destinations)) = m_pre)) (PreH12 : (Forall (Z.le (0)) dist )) (PreH13 : (Forall (Z.ge (100)) dist )) (PreH14 : (Forall (Z.le (0)) times )) (PreH15 : (Forall (Z.ge (100000)) times )) (PreH16 : (Forall (Z.le (1)) origins )) (PreH17 : (Forall (Z.ge (n_pre)) destinations )) (PreH18 : (Forall2 Z.lt origins destinations )) (PreH19 : (0 <= k_pre)) (PreH20 : (k_pre <= 100000)) (PreH21 : ((Zlength (latest)) = n_pre)) (PreH22 : ((Zlength (counts)) = n_pre)) (PreH23 : (Forall (Z.le (0)) latest )) (PreH24 : (Forall (Z.ge (100000)) latest )) (PreH25 : (Forall (Z.le (0)) counts )) (PreH26 : (Forall (Z.ge (i)) counts )) (PreH27 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i destinations 0))
  **  (IntArray.missing_i b_pre i 0 m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH2 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) = ((Znth (i) (origins) (0)) - 1 ))) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (((Znth (i) (destinations) (0)) - 1 ) = ((Znth (i) (destinations) (0)) - 1 ))) (PreH7 : (k_pre <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (i < m_pre)) (PreH14 : (0 <= i)) (PreH15 : (i <= m_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : (0 <= k_pre)) (PreH32 : (k_pre <= 100000)) (PreH33 : ((Zlength (latest)) = n_pre)) (PreH34 : ((Zlength (counts)) = n_pre)) (PreH35 : (Forall (Z.le (0)) latest )) (PreH36 : (Forall (Z.ge (100000)) latest )) (PreH37 : (Forall (Z.le (0)) counts )) (PreH38 : (Forall (Z.ge (i)) counts )) (PreH39 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((( &( "late" ) ) + (((Znth (i) (origins) (0)) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth (i) (origins) (0)) - 1 ) latest 0))
  **  (IntArray.missing_i ( &( "late" ) ) ((Znth (i) (origins) (0)) - 1 ) 0 n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH2 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH3 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH4 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH5 : (k_pre <= INT_MAX)) (PreH6 : (m_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= m_pre)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 1000)) (PreH16 : (1 <= m_pre)) (PreH17 : (m_pre <= 10000)) (PreH18 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH19 : ((Zlength (times)) = m_pre)) (PreH20 : ((Zlength (origins)) = m_pre)) (PreH21 : ((Zlength (destinations)) = m_pre)) (PreH22 : (Forall (Z.le (0)) dist )) (PreH23 : (Forall (Z.ge (100)) dist )) (PreH24 : (Forall (Z.le (0)) times )) (PreH25 : (Forall (Z.ge (100000)) times )) (PreH26 : (Forall (Z.le (1)) origins )) (PreH27 : (Forall (Z.ge (n_pre)) destinations )) (PreH28 : (Forall2 Z.lt origins destinations )) (PreH29 : (0 <= k_pre)) (PreH30 : (k_pre <= 100000)) (PreH31 : ((Zlength (latest)) = n_pre)) (PreH32 : ((Zlength (counts)) = n_pre)) (PreH33 : (Forall (Z.le (0)) latest )) (PreH34 : (Forall (Z.ge (100000)) latest )) (PreH35 : (Forall (Z.le (0)) counts )) (PreH36 : (Forall (Z.ge (i)) counts )) (PreH37 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((t_pre + (i * sizeof(INT)))) # Int  |-> (Znth i times 0))
  **  (IntArray.missing_i t_pre i 0 m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((t_pre + (i * sizeof(INT)))) # Int  |-> (Znth i times 0))
  **  (IntArray.missing_i t_pre i 0 m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((( &( "late" ) ) + (((Znth (i) (origins) (0)) - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "late" ) ) ((Znth (i) (origins) (0)) - 1 ) 0 n_pre latest )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((( &( "off" ) ) + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0))
  **  (IntArray.missing_i ( &( "off" ) ) ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) < (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((( &( "off" ) ) + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "off" ) ) ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full ( &( "late" ) ) n_pre (replace_Znth (((Znth (i) (origins) (0)) - 1 )) ((Znth i times 0)) (latest)) )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((( &( "off" ) ) + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth (i) (destinations) (0)) - 1 ) counts 0))
  **  (IntArray.missing_i ( &( "off" ) ) ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0))) (PreH2 : (0 <= ((Znth (i) (origins) (0)) - 1 ))) (PreH3 : (((Znth (i) (origins) (0)) - 1 ) < n_pre)) (PreH4 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH5 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH6 : (k_pre <= INT_MAX)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (k_pre >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (i < m_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= m_pre)) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 1000)) (PreH17 : (1 <= m_pre)) (PreH18 : (m_pre <= 10000)) (PreH19 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH20 : ((Zlength (times)) = m_pre)) (PreH21 : ((Zlength (origins)) = m_pre)) (PreH22 : ((Zlength (destinations)) = m_pre)) (PreH23 : (Forall (Z.le (0)) dist )) (PreH24 : (Forall (Z.ge (100)) dist )) (PreH25 : (Forall (Z.le (0)) times )) (PreH26 : (Forall (Z.ge (100000)) times )) (PreH27 : (Forall (Z.le (1)) origins )) (PreH28 : (Forall (Z.ge (n_pre)) destinations )) (PreH29 : (Forall2 Z.lt origins destinations )) (PreH30 : (0 <= k_pre)) (PreH31 : (k_pre <= 100000)) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (i)) counts )) (PreH38 : (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((Znth ((Znth (i) (origins) (0)) - 1 ) latest 0) >= (Znth i times 0)) ” 
  &&  “ (0 <= ((Znth (i) (origins) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (origins) (0)) - 1 ) < n_pre) ” 
  &&  “ (0 <= ((Znth (i) (destinations) (0)) - 1 )) ” 
  &&  “ (((Znth (i) (destinations) (0)) - 1 ) < n_pre) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (m_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (i)) counts ) ” 
  &&  “ (PassengerAggregationPrefix n_pre m_pre times origins destinations i latest counts ) ”
  &&  (((( &( "off" ) ) + (((Znth (i) (destinations) (0)) - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "off" ) ) ((Znth (i) (destinations) (0)) - 1 ) 0 n_pre counts )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_full ( &( "arr" ) ) n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) (PreH24 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH25 : (Forall (Z.le (0)) latest )) (PreH26 : (Forall (Z.ge (100000)) latest )) (PreH27 : (Forall (Z.le (0)) counts )) (PreH28 : (Forall (Z.ge (m_pre)) counts )) (PreH29 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 i arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) i n_pre )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((( &( "arr" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.seg ( &( "arr" ) ) 0 i arrivals_prefix )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= cur)) (PreH5 : (cur <= 200000)) (PreH6 : ((Zlength (arrivals_prefix)) = i)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre <= 10000)) (PreH11 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH12 : ((Zlength (times)) = m_pre)) (PreH13 : ((Zlength (origins)) = m_pre)) (PreH14 : ((Zlength (destinations)) = m_pre)) (PreH15 : (Forall (Z.le (0)) dist )) (PreH16 : (Forall (Z.ge (100)) dist )) (PreH17 : (Forall (Z.le (0)) times )) (PreH18 : (Forall (Z.ge (100000)) times )) (PreH19 : (Forall (Z.le (1)) origins )) (PreH20 : (Forall (Z.ge (n_pre)) destinations )) (PreH21 : (Forall2 Z.lt origins destinations )) (PreH22 : (0 <= k_pre)) (PreH23 : (k_pre <= 100000)) (PreH24 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH25 : (Forall (Z.le (0)) latest )) (PreH26 : (Forall (Z.ge (100000)) latest )) (PreH27 : (Forall (Z.le (0)) counts )) (PreH28 : (Forall (Z.ge (m_pre)) counts )) (PreH29 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((( &( "late" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i latest 0))
  **  (IntArray.missing_i ( &( "late" ) ) i 0 n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : (cur < (Znth i latest 0))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= cur)) (PreH6 : (cur <= 200000)) (PreH7 : ((Zlength (arrivals_prefix)) = i)) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 1000)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre <= 10000)) (PreH12 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH13 : ((Zlength (times)) = m_pre)) (PreH14 : ((Zlength (origins)) = m_pre)) (PreH15 : ((Zlength (destinations)) = m_pre)) (PreH16 : (Forall (Z.le (0)) dist )) (PreH17 : (Forall (Z.ge (100)) dist )) (PreH18 : (Forall (Z.le (0)) times )) (PreH19 : (Forall (Z.ge (100000)) times )) (PreH20 : (Forall (Z.le (1)) origins )) (PreH21 : (Forall (Z.ge (n_pre)) destinations )) (PreH22 : (Forall2 Z.lt origins destinations )) (PreH23 : (0 <= k_pre)) (PreH24 : (k_pre <= 100000)) (PreH25 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH26 : (Forall (Z.le (0)) latest )) (PreH27 : (Forall (Z.ge (100000)) latest )) (PreH28 : (Forall (Z.le (0)) counts )) (PreH29 : (Forall (Z.ge (m_pre)) counts )) (PreH30 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ (cur < (Znth i latest 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((( &( "late" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i latest 0))
  **  (IntArray.missing_i ( &( "late" ) ) i 0 n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur < (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) < n_pre) ” 
  &&  “ (cur < (Znth i latest 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i dist 0))
  **  (IntArray.missing_i d_pre i 0 (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_17 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals_prefix: (@list Z)) (cur: Z) (i: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (cur >= (Znth i latest 0))) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cur)) (PreH7 : (cur <= 200000)) (PreH8 : ((Zlength (arrivals_prefix)) = i)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : (1 <= m_pre)) (PreH12 : (m_pre <= 10000)) (PreH13 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH14 : ((Zlength (times)) = m_pre)) (PreH15 : ((Zlength (origins)) = m_pre)) (PreH16 : ((Zlength (destinations)) = m_pre)) (PreH17 : (Forall (Z.le (0)) dist )) (PreH18 : (Forall (Z.ge (100)) dist )) (PreH19 : (Forall (Z.le (0)) times )) (PreH20 : (Forall (Z.ge (100000)) times )) (PreH21 : (Forall (Z.le (1)) origins )) (PreH22 : (Forall (Z.ge (n_pre)) destinations )) (PreH23 : (Forall2 Z.lt origins destinations )) (PreH24 : (0 <= k_pre)) (PreH25 : (k_pre <= 100000)) (PreH26 : (StationSummaryState n_pre m_pre times origins destinations latest counts )) (PreH27 : (Forall (Z.le (0)) latest )) (PreH28 : (Forall (Z.ge (100000)) latest )) (PreH29 : (Forall (Z.le (0)) counts )) (PreH30 : (Forall (Z.ge (m_pre)) counts )) (PreH31 : (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur )) ,
  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full d_pre (n_pre - 1 ) dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
|--
  “ ((i + 1 ) < n_pre) ” 
  &&  “ (cur >= (Znth i latest 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 200000) ” 
  &&  “ ((Zlength (arrivals_prefix)) = i) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= 100000) ” 
  &&  “ (StationSummaryState n_pre m_pre times origins destinations latest counts ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (ArrivalSimulationPrefix n_pre dist latest arrivals_prefix i cur ) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i dist 0))
  **  (IntArray.missing_i d_pre i 0 (n_pre - 1 ) dist )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.seg ( &( "arr" ) ) 0 (i + 1 ) (app (arrivals_prefix) ((cons (cur) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "arr" ) ) (i + 1 ) n_pre )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_18 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : ((i + 1 ) < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 1 ))) (PreH7 : (0 <= best)) (PreH8 : (best <= m_pre)) (PreH9 : ((-1) <= pos)) (PreH10 : (pos < i)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (latest)) = n_pre)) (PreH28 : ((Zlength (counts)) = n_pre)) (PreH29 : ((Zlength (arrivals)) = n_pre)) (PreH30 : (Forall (Z.le (0)) current_dist )) (PreH31 : (Forall (Z.ge (100)) current_dist )) (PreH32 : (Forall (Z.le (0)) latest )) (PreH33 : (Forall (Z.ge (100000)) latest )) (PreH34 : (Forall (Z.le (0)) counts )) (PreH35 : (Forall (Z.ge (m_pre)) counts )) (PreH36 : (Forall (Z.le (0)) arrivals )) (PreH37 : (Forall (Z.ge (200000)) arrivals )) (PreH38 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH39 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ”
  &&  (((d_pre + (i * sizeof(INT)))) # Int  |-> (Znth i current_dist 0))
  **  (IntArray.missing_i d_pre i 0 (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_19 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : ((Zlength (arrivals)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist )) (PreH36 : (Forall (Z.ge (100)) current_dist )) (PreH37 : (Forall (Z.le (0)) latest )) (PreH38 : (Forall (Z.ge (100000)) latest )) (PreH39 : (Forall (Z.le (0)) counts )) (PreH40 : (Forall (Z.ge (m_pre)) counts )) (PreH41 : (Forall (Z.le (0)) arrivals )) (PreH42 : (Forall (Z.ge (200000)) arrivals )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH44 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH45 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i j cnt ) ”
  &&  (((( &( "off" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j counts 0))
  **  (IntArray.missing_i ( &( "off" ) ) j 0 n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_20 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : ((Zlength (arrivals)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist )) (PreH36 : (Forall (Z.ge (100)) current_dist )) (PreH37 : (Forall (Z.le (0)) latest )) (PreH38 : (Forall (Z.ge (100000)) latest )) (PreH39 : (Forall (Z.le (0)) counts )) (PreH40 : (Forall (Z.ge (m_pre)) counts )) (PreH41 : (Forall (Z.le (0)) arrivals )) (PreH42 : (Forall (Z.ge (200000)) arrivals )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH44 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH45 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i j cnt ) ”
  &&  (((( &( "arr" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j arrivals 0))
  **  (IntArray.missing_i ( &( "arr" ) ) j 0 n_pre arrivals )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_21 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (cnt: Z) (j: Z) (i: Z) (k: Z) (PreH1 : (j < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= i)) (PreH6 : (i < (n_pre - 1 ))) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt <= m_pre)) (PreH11 : (0 <= best)) (PreH12 : (best <= m_pre)) (PreH13 : ((-1) <= pos)) (PreH14 : (pos < i)) (PreH15 : (0 < (Znth (i) (current_dist) (0)))) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre <= 1000)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre <= 10000)) (PreH20 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH21 : ((Zlength (times)) = m_pre)) (PreH22 : ((Zlength (origins)) = m_pre)) (PreH23 : ((Zlength (destinations)) = m_pre)) (PreH24 : (Forall (Z.le (0)) dist )) (PreH25 : (Forall (Z.ge (100)) dist )) (PreH26 : (Forall (Z.le (0)) times )) (PreH27 : (Forall (Z.ge (100000)) times )) (PreH28 : (Forall (Z.le (1)) origins )) (PreH29 : (Forall (Z.ge (n_pre)) destinations )) (PreH30 : (Forall2 Z.lt origins destinations )) (PreH31 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH32 : ((Zlength (latest)) = n_pre)) (PreH33 : ((Zlength (counts)) = n_pre)) (PreH34 : ((Zlength (arrivals)) = n_pre)) (PreH35 : (Forall (Z.le (0)) current_dist )) (PreH36 : (Forall (Z.ge (100)) current_dist )) (PreH37 : (Forall (Z.le (0)) latest )) (PreH38 : (Forall (Z.ge (100000)) latest )) (PreH39 : (Forall (Z.le (0)) counts )) (PreH40 : (Forall (Z.ge (m_pre)) counts )) (PreH41 : (Forall (Z.le (0)) arrivals )) (PreH42 : (Forall (Z.ge (200000)) arrivals )) (PreH43 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH44 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) (PreH45 : (MarginalBenefitScan counts latest arrivals i j cnt )) ,
  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ” 
  &&  “ (MarginalBenefitScan counts latest arrivals i j cnt ) ”
  &&  (((( &( "late" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j latest 0))
  **  (IntArray.missing_i ( &( "late" ) ) j 0 n_pre latest )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_22 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ”
  &&  (((d_pre + (pos * sizeof(INT)))) # Int  |-> (Znth pos current_dist 0))
  **  (IntArray.missing_i d_pre pos 0 (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_23 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (arrivals: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (current_dist: (@list Z)) (pos: Z) (best: Z) (i: Z) (k: Z) (PreH1 : (best <> 0)) (PreH2 : (pos >= 0)) (PreH3 : ((i + 1 ) >= n_pre)) (PreH4 : (0 < k)) (PreH5 : (k <= k_pre)) (PreH6 : (k_pre <= 100000)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (0 <= best)) (PreH10 : (best <= m_pre)) (PreH11 : ((-1) <= pos)) (PreH12 : (pos < i)) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 1000)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre <= 10000)) (PreH17 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH18 : ((Zlength (times)) = m_pre)) (PreH19 : ((Zlength (origins)) = m_pre)) (PreH20 : ((Zlength (destinations)) = m_pre)) (PreH21 : (Forall (Z.le (0)) dist )) (PreH22 : (Forall (Z.ge (100)) dist )) (PreH23 : (Forall (Z.le (0)) times )) (PreH24 : (Forall (Z.ge (100000)) times )) (PreH25 : (Forall (Z.le (1)) origins )) (PreH26 : (Forall (Z.ge (n_pre)) destinations )) (PreH27 : (Forall2 Z.lt origins destinations )) (PreH28 : ((Zlength (current_dist)) = (n_pre - 1 ))) (PreH29 : ((Zlength (latest)) = n_pre)) (PreH30 : ((Zlength (counts)) = n_pre)) (PreH31 : ((Zlength (arrivals)) = n_pre)) (PreH32 : (Forall (Z.le (0)) current_dist )) (PreH33 : (Forall (Z.ge (100)) current_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) arrivals )) (PreH39 : (Forall (Z.ge (200000)) arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals )) (PreH41 : (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos )) ,
  (IntArray.full d_pre (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (current_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) current_dist ) ” 
  &&  “ (Forall (Z.ge (100)) current_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations current_dist latest counts arrivals ) ” 
  &&  “ (EdgeChoicePrefix n_pre current_dist counts latest arrivals i best pos ) ”
  &&  (((d_pre + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i d_pre pos 0 (n_pre - 1 ) current_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_24 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) new_dist ) ” 
  &&  “ (Forall (Z.ge (100)) new_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) new_arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) new_arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((( &( "arr" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i new_arrivals 0))
  **  (IntArray.missing_i ( &( "arr" ) ) i 0 n_pre new_arrivals )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_25 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre new_arrivals )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) new_dist ) ” 
  &&  “ (Forall (Z.ge (100)) new_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) new_arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) new_arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((( &( "arr" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "arr" ) ) i 0 n_pre new_arrivals )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_26 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) new_dist ) ” 
  &&  “ (Forall (Z.ge (100)) new_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) new_arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) new_arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((( &( "arr" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) 0))
  **  (IntArray.missing_i ( &( "arr" ) ) i 0 n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_27 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (counts: (@list Z)) (latest: (@list Z)) (new_arrivals: (@list Z)) (old_arrivals: (@list Z)) (new_dist: (@list Z)) (old_dist: (@list Z)) (i: Z) (best: Z) (pos: Z) (k: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 < k)) (PreH3 : (k <= k_pre)) (PreH4 : (k_pre <= 100000)) (PreH5 : (0 <= pos)) (PreH6 : (pos < (n_pre - 1 ))) (PreH7 : (0 < best)) (PreH8 : (best <= m_pre)) (PreH9 : ((pos + 1 ) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : (1 <= m_pre)) (PreH14 : (m_pre <= 10000)) (PreH15 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH16 : ((Zlength (times)) = m_pre)) (PreH17 : ((Zlength (origins)) = m_pre)) (PreH18 : ((Zlength (destinations)) = m_pre)) (PreH19 : (Forall (Z.le (0)) dist )) (PreH20 : (Forall (Z.ge (100)) dist )) (PreH21 : (Forall (Z.le (0)) times )) (PreH22 : (Forall (Z.ge (100000)) times )) (PreH23 : (Forall (Z.le (1)) origins )) (PreH24 : (Forall (Z.ge (n_pre)) destinations )) (PreH25 : (Forall2 Z.lt origins destinations )) (PreH26 : ((Zlength (old_dist)) = (n_pre - 1 ))) (PreH27 : ((Zlength (new_dist)) = (n_pre - 1 ))) (PreH28 : ((Zlength (old_arrivals)) = n_pre)) (PreH29 : ((Zlength (new_arrivals)) = n_pre)) (PreH30 : ((Zlength (latest)) = n_pre)) (PreH31 : ((Zlength (counts)) = n_pre)) (PreH32 : (Forall (Z.le (0)) new_dist )) (PreH33 : (Forall (Z.ge (100)) new_dist )) (PreH34 : (Forall (Z.le (0)) latest )) (PreH35 : (Forall (Z.ge (100000)) latest )) (PreH36 : (Forall (Z.le (0)) counts )) (PreH37 : (Forall (Z.ge (m_pre)) counts )) (PreH38 : (Forall (Z.le (0)) new_arrivals )) (PreH39 : (Forall (Z.ge (200000)) new_arrivals )) (PreH40 : (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals )) (PreH41 : (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos )) (PreH42 : (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i )) ,
  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ ((Zlength (old_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (new_dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (old_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (new_arrivals)) = n_pre) ” 
  &&  “ ((Zlength (latest)) = n_pre) ” 
  &&  “ ((Zlength (counts)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) new_dist ) ” 
  &&  “ (Forall (Z.ge (100)) new_dist ) ” 
  &&  “ (Forall (Z.le (0)) latest ) ” 
  &&  “ (Forall (Z.ge (100000)) latest ) ” 
  &&  “ (Forall (Z.le (0)) counts ) ” 
  &&  “ (Forall (Z.ge (m_pre)) counts ) ” 
  &&  “ (Forall (Z.le (0)) new_arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) new_arrivals ) ” 
  &&  “ (BoosterProgress n_pre m_pre k_pre k dist times origins destinations old_dist latest counts old_arrivals ) ” 
  &&  “ (BestBoostChoice n_pre old_dist counts latest old_arrivals best pos ) ” 
  &&  “ (ArrivalRepairProgress n_pre old_dist old_arrivals new_dist new_arrivals latest pos i ) ”
  &&  (((( &( "late" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i latest 0))
  **  (IntArray.missing_i ( &( "late" ) ) i 0 n_pre latest )
  **  (IntArray.full ( &( "arr" ) ) n_pre (replace_Znth (i) (((Znth i new_arrivals 0) - 1 )) (new_arrivals)) )
  **  (IntArray.full d_pre (n_pre - 1 ) new_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_28 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i destinations 0))
  **  (IntArray.missing_i b_pre i 0 m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_29 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  (((( &( "arr" ) ) + (((Znth i destinations 0) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i destinations 0) - 1 ) arrivals 0))
  **  (IntArray.missing_i ( &( "arr" ) ) ((Znth i destinations 0) - 1 ) 0 n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
.

Definition solve_partial_solve_wit_30 := 
forall (b_pre: Z) (a_pre: Z) (t_pre: Z) (d_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (destinations: (@list Z)) (origins: (@list Z)) (times: (@list Z)) (dist: (@list Z)) (final_dist: (@list Z)) (latest: (@list Z)) (counts: (@list Z)) (arrivals: (@list Z)) (ans: Z) (i: Z) (k: Z) (PreH1 : (0 <= ((Znth (i) (destinations) (0)) - 1 ))) (PreH2 : (((Znth (i) (destinations) (0)) - 1 ) < n_pre)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (ans >= INT_MIN)) (PreH8 : (k >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (i < m_pre)) (PreH12 : (0 <= k)) (PreH13 : (k <= k_pre)) (PreH14 : (k_pre <= 100000)) (PreH15 : (0 <= i)) (PreH16 : (i <= m_pre)) (PreH17 : (0 <= ans)) (PreH18 : (ans <= (i * 200000 ))) (PreH19 : (ans <= 2000000000)) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 1000)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre <= 10000)) (PreH24 : ((Zlength (dist)) = (n_pre - 1 ))) (PreH25 : ((Zlength (times)) = m_pre)) (PreH26 : ((Zlength (origins)) = m_pre)) (PreH27 : ((Zlength (destinations)) = m_pre)) (PreH28 : (Forall (Z.le (0)) dist )) (PreH29 : (Forall (Z.ge (100)) dist )) (PreH30 : (Forall (Z.le (0)) times )) (PreH31 : (Forall (Z.ge (100000)) times )) (PreH32 : (Forall (Z.le (1)) origins )) (PreH33 : (Forall (Z.ge (n_pre)) destinations )) (PreH34 : (Forall2 Z.lt origins destinations )) (PreH35 : (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals )) (PreH36 : ((Zlength (arrivals)) = n_pre)) (PreH37 : (Forall (Z.le (0)) arrivals )) (PreH38 : (Forall (Z.ge (200000)) arrivals )) (PreH39 : (Forall (Z.le (1)) destinations )) (PreH40 : (TravelSumPrefix m_pre times destinations arrivals i ans )) ,
  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full t_pre m_pre times )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 10000) ” 
  &&  “ ((Zlength (dist)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (times)) = m_pre) ” 
  &&  “ ((Zlength (origins)) = m_pre) ” 
  &&  “ ((Zlength (destinations)) = m_pre) ” 
  &&  “ (Forall (Z.le (0)) dist ) ” 
  &&  “ (Forall (Z.ge (100)) dist ) ” 
  &&  “ (Forall (Z.le (0)) times ) ” 
  &&  “ (Forall (Z.ge (100000)) times ) ” 
  &&  “ (Forall (Z.le (1)) origins ) ” 
  &&  “ (Forall (Z.ge (n_pre)) destinations ) ” 
  &&  “ (Forall2 Z.lt origins destinations ) ” 
  &&  “ (OptimizedBusState n_pre m_pre k_pre dist times origins destinations final_dist latest counts arrivals ) ” 
  &&  “ ((Zlength (arrivals)) = n_pre) ” 
  &&  “ (Forall (Z.le (0)) arrivals ) ” 
  &&  “ (Forall (Z.ge (200000)) arrivals ) ” 
  &&  “ (Forall (Z.le (1)) destinations ) ” 
  &&  “ (TravelSumPrefix m_pre times destinations arrivals i ans ) ”
  &&  (((t_pre + (i * sizeof(INT)))) # Int  |-> (Znth i times 0))
  **  (IntArray.missing_i t_pre i 0 m_pre times )
  **  (IntArray.full ( &( "arr" ) ) n_pre arrivals )
  **  (IntArray.full b_pre m_pre destinations )
  **  (IntArray.full d_pre (n_pre - 1 ) final_dist )
  **  (IntArray.full a_pre m_pre origins )
  **  (IntArray.full ( &( "late" ) ) n_pre latest )
  **  (IntArray.undef_seg ( &( "late" ) ) n_pre 1000 )
  **  (IntArray.full ( &( "off" ) ) n_pre counts )
  **  (IntArray.undef_seg ( &( "off" ) ) n_pre 1000 )
  **  (IntArray.undef_seg ( &( "arr" ) ) n_pre 1000 )
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
Axiom proof_of_solve_safety_wit_66 : solve_safety_wit_66.
Axiom proof_of_solve_safety_wit_67 : solve_safety_wit_67.
Axiom proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Axiom proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Axiom proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Axiom proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Axiom proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1.
Axiom proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2.
Axiom proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Axiom proof_of_solve_entail_wit_7_1 : solve_entail_wit_7_1.
Axiom proof_of_solve_entail_wit_7_2 : solve_entail_wit_7_2.
Axiom proof_of_solve_entail_wit_7_3 : solve_entail_wit_7_3.
Axiom proof_of_solve_entail_wit_7_4 : solve_entail_wit_7_4.
Axiom proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Axiom proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Axiom proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Axiom proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Axiom proof_of_solve_entail_wit_12_1 : solve_entail_wit_12_1.
Axiom proof_of_solve_entail_wit_12_2 : solve_entail_wit_12_2.
Axiom proof_of_solve_entail_wit_13_1 : solve_entail_wit_13_1.
Axiom proof_of_solve_entail_wit_13_2 : solve_entail_wit_13_2.
Axiom proof_of_solve_entail_wit_13_3 : solve_entail_wit_13_3.
Axiom proof_of_solve_entail_wit_14 : solve_entail_wit_14.
Axiom proof_of_solve_entail_wit_15 : solve_entail_wit_15.
Axiom proof_of_solve_entail_wit_16_1 : solve_entail_wit_16_1.
Axiom proof_of_solve_entail_wit_16_2 : solve_entail_wit_16_2.
Axiom proof_of_solve_entail_wit_17_1 : solve_entail_wit_17_1.
Axiom proof_of_solve_entail_wit_17_2 : solve_entail_wit_17_2.
Axiom proof_of_solve_entail_wit_17_3 : solve_entail_wit_17_3.
Axiom proof_of_solve_entail_wit_18 : solve_entail_wit_18.
Axiom proof_of_solve_entail_wit_19 : solve_entail_wit_19.
Axiom proof_of_solve_entail_wit_20 : solve_entail_wit_20.
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
