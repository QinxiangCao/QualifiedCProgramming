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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> forall (j: Z) , (((0 <= j) /\ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) 0) = 67) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 77)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 89)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 87)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 71)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 66))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (n_pre = (Zlength (photo)))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100)) (PreH6 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH7 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH8 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre * m_pre ))) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ ((n_pre * m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * m_pre )) ”
.

Definition solver_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < (n_pre * m_pre ))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH9 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre * m_pre ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (67 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 67) ”
.

Definition solver_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) <> 67)) (PreH2 : (i < (n_pre * m_pre ))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH10 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre * m_pre ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (77 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 77) ”
.

Definition solver_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) <> 77)) (PreH2 : ((Znth i (concat (photo)) 0) <> 67)) (PreH3 : (i < (n_pre * m_pre ))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH11 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre * m_pre ))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (89 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 89) ”
.

Definition solver_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 77)) (PreH2 : ((Znth i (concat (photo)) 0) <> 67)) (PreH3 : (i < (n_pre * m_pre ))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH11 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre * m_pre ))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 67)) (PreH2 : (i < (n_pre * m_pre ))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH10 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre * m_pre ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 89)) (PreH2 : ((Znth i (concat (photo)) 0) <> 77)) (PreH3 : ((Znth i (concat (photo)) 0) <> 67)) (PreH4 : (i < (n_pre * m_pre ))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH12 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre * m_pre ))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= (n_pre * m_pre ))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH9 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre * m_pre ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) <> 89)) (PreH2 : ((Znth i (concat (photo)) 0) <> 77)) (PreH3 : ((Znth i (concat (photo)) 0) <> 67)) (PreH4 : (i < (n_pre * m_pre ))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH12 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre * m_pre ))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> forall (j: Z) , (((0 <= j) /\ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) 0) = 67) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 77)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 89)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 87)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 71)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 66))))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ (n_pre = (Zlength (photo))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66)))) ” 
  &&  “ ((Zlength ((concat (photo)))) = (n_pre * m_pre )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre * m_pre )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89))) ”
  &&  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> forall (j: Z) , (((0 <= j) /\ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) 0) = 67) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 77)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 89)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 87)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 71)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 66))))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89))) ” 
  &&  “ ((Zlength ((concat (photo)))) = (n_pre * m_pre )) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66)))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> forall (j: Z) , (((0 <= j) /\ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) 0) = 67) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 77)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 89)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 87)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 71)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 66))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> forall (j: Z) , (((0 <= j) /\ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) 0) = 67) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 77)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 89)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 87)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 71)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 66))))) ,
  ((Zlength ((concat (photo)))) = (n_pre * m_pre ))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> forall (j: Z) , (((0 <= j) /\ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) 0) = 67) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 77)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 89)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 87)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 71)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 66))))) ,
  forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z)))  __default__List_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100)) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Zlength ((Znth i photo __default__List_Z))) = m_pre))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> forall (j: Z) , (((0 <= j) /\ (j < m_pre)) -> (((((((Znth j (Znth i_2 photo __default__List_Z) 0) = 67) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 77)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 89)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 87)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 71)) \/ ((Znth j (Znth i_2 photo __default__List_Z) 0) = 66))))) ,
  forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))
.

Definition solver_entail_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) <> 89)) (PreH2 : ((Znth i (concat (photo)) 0) <> 77)) (PreH3 : ((Znth i (concat (photo)) 0) <> 67)) (PreH4 : (i < (n_pre * m_pre ))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH12 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre * m_pre ))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ (n_pre = (Zlength (photo))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66)))) ” 
  &&  “ ((Zlength ((concat (photo)))) = (n_pre * m_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre * m_pre )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89))) ”
  &&  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
.

Definition solver_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= (n_pre * m_pre ))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH9 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre * m_pre ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= (n_pre * m_pre ))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH9 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre * m_pre ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  TT && emp 
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 0 ) ”
  &&  emp
).

Definition solver_return_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 77)) (PreH2 : ((Znth i (concat (photo)) 0) <> 67)) (PreH3 : (i < (n_pre * m_pre ))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH11 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre * m_pre ))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 77)) (PreH2 : ((Znth i (concat (photo)) 0) <> 67)) (PreH3 : (i < (n_pre * m_pre ))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH11 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre * m_pre ))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  TT && emp 
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  emp
).

Definition solver_return_wit_3 := 
(
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 67)) (PreH2 : (i < (n_pre * m_pre ))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH10 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre * m_pre ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 67)) (PreH2 : (i < (n_pre * m_pre ))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH10 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre * m_pre ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  TT && emp 
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  emp
).

Definition solver_return_wit_4 := 
(
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 89)) (PreH2 : ((Znth i (concat (photo)) 0) <> 77)) (PreH3 : ((Znth i (concat (photo)) 0) <> 67)) (PreH4 : (i < (n_pre * m_pre ))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH12 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre * m_pre ))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) = 89)) (PreH2 : ((Znth i (concat (photo)) 0) <> 77)) (PreH3 : ((Znth i (concat (photo)) 0) <> 67)) (PreH4 : (i < (n_pre * m_pre ))) (PreH5 : (n_pre = (Zlength (photo)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre <= 100)) (PreH10 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH11 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH12 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre * m_pre ))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  TT && emp 
|--
  EX (out: bool) ,
  “ (Spec photo out ) ” 
  &&  “ (SolverReturnBridge out 1 ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < (n_pre * m_pre ))) (PreH2 : (n_pre = (Zlength (photo)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH8 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH9 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre * m_pre ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ (i < (n_pre * m_pre )) ” 
  &&  “ (n_pre = (Zlength (photo))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66)))) ” 
  &&  “ ((Zlength ((concat (photo)))) = (n_pre * m_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre * m_pre )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89))) ”
  &&  (((px_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (concat (photo)) 0))
  **  (CharArray.missing_i px_pre i 0 (n_pre * m_pre ) (concat (photo)) )
.

Definition solver_partial_solve_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) <> 67)) (PreH2 : (i < (n_pre * m_pre ))) (PreH3 : (n_pre = (Zlength (photo)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100)) (PreH8 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH9 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH10 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre * m_pre ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ ((Znth i (concat (photo)) 0) <> 67) ” 
  &&  “ (i < (n_pre * m_pre )) ” 
  &&  “ (n_pre = (Zlength (photo))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66)))) ” 
  &&  “ ((Zlength ((concat (photo)))) = (n_pre * m_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre * m_pre )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89))) ”
  &&  (((px_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (concat (photo)) 0))
  **  (CharArray.missing_i px_pre i 0 (n_pre * m_pre ) (concat (photo)) )
.

Definition solver_partial_solve_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (px_pre: Z) (photo: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Znth i (concat (photo)) 0) <> 77)) (PreH2 : ((Znth i (concat (photo)) 0) <> 67)) (PreH3 : (i < (n_pre * m_pre ))) (PreH4 : (n_pre = (Zlength (photo)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre <= 100)) (PreH9 : forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre))) (PreH10 : forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66))))) (PreH11 : ((Zlength ((concat (photo)))) = (n_pre * m_pre ))) (PreH12 : (0 <= i)) (PreH13 : (i <= (n_pre * m_pre ))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89)))) ,
  (CharArray.full px_pre (n_pre * m_pre ) (concat (photo)) )
|--
  “ ((Znth i (concat (photo)) 0) <> 77) ” 
  &&  “ ((Znth i (concat (photo)) 0) <> 67) ” 
  &&  “ (i < (n_pre * m_pre )) ” 
  &&  “ (n_pre = (Zlength (photo))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < n_pre)) -> ((Zlength ((Znth r photo __default__List_Z))) = m_pre)) ” 
  &&  “ forall (r_2: Z) , (((0 <= r_2) /\ (r_2 < n_pre)) -> forall (c: Z) , (((0 <= c) /\ (c < m_pre)) -> (((((((Znth c (Znth r_2 photo __default__List_Z) 0) = 67) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 77)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 89)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 87)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 71)) \/ ((Znth c (Znth r_2 photo __default__List_Z) 0) = 66)))) ” 
  &&  “ ((Zlength ((concat (photo)))) = (n_pre * m_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre * m_pre )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((((Znth k (concat (photo)) 0) <> 67) /\ ((Znth k (concat (photo)) 0) <> 77)) /\ ((Znth k (concat (photo)) 0) <> 89))) ”
  &&  (((px_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (concat (photo)) 0))
  **  (CharArray.missing_i px_pre i 0 (n_pre * m_pre ) (concat (photo)) )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
