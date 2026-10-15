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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P041_1054C_candies_distribution_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (PreH1 : (1 <= (Zlength (l_data)))) (PreH2 : ((Zlength (l_data)) <= 1000)) (PreH3 : ((Zlength (r_data)) = (Zlength (l_data)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (l_data)))) -> ((0 <= (Znth i l_data 0)) /\ ((Znth i l_data 0) <= (Zlength (l_data)))))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (r_data)))) -> ((0 <= (Znth i_2 r_data 0)) /\ ((Znth i_2 r_data 0) <= (Zlength (l_data)))))) (PreH6 : (n_pre = (Zlength (l_data)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.undef_full a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.seg a_pre 0 (i + 1 ) (app (prefix) ((cons (((n_pre - (Znth i l_data 0) ) - (Znth i r_data 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ (((n_pre - (Znth i l_data 0) ) - (Znth i r_data 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre - (Znth i l_data 0) ) - (Znth i r_data 0) )) ”
.

Definition solver_safety_wit_4 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.full l_pre n_pre l_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ ((n_pre - (Znth i l_data 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - (Znth i l_data 0) )) ”
.

Definition solver_safety_wit_5 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate i )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "cl" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate i )) ,
  ((( &( "cl" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate i )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> 0)
  **  ((( &( "cl" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) <= (Znth i candidate 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i j cl )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> (cl + 0 ))
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) > (Znth i candidate 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i j cl )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> (cl + 1 ))
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) > (Znth i candidate 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i j cl )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((cl + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cl + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) <= (Znth i candidate 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i j cl )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((cl + 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cl + 0 )) ”
.

Definition solver_safety_wit_13 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH17 : (CandyLeftCount candidate i j cl )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH17 : (CandyLeftCount candidate i j cl )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) <= (Znth i candidate 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> (cr + 0 ))
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) > (Znth i candidate 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> (cr + 1 ))
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) > (Znth i candidate 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((cr + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cr + 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth j candidate 0) <= (Znth i candidate 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((cr + 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cr + 0 )) ”
.

Definition solver_safety_wit_19 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= i)) (PreH15 : (0 <= cr)) (PreH16 : (cr <= (j - (i + 1 ) ))) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i i cl )) (PreH19 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_20 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cl <> (Znth i l_data 0))) (PreH2 : ((Znth i candidate 0) >= 1)) (PreH3 : (j >= n_pre)) (PreH4 : (n_pre = (Zlength (l_data)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (r_data)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 <= cl)) (PreH16 : (cl <= i)) (PreH17 : (0 <= cr)) (PreH18 : (cr <= (j - (i + 1 ) ))) (PreH19 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH20 : (CandyLeftCount candidate i i cl )) (PreH21 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth i candidate 0) < 1)) (PreH2 : (j >= n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_22 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cr <> (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH21 : (CandyLeftCount candidate i i cl )) (PreH22 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # Int  |-> cl)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cr = (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH21 : (CandyLeftCount candidate i i cl )) (PreH22 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate i )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (PreH1 : (1 <= (Zlength (l_data)))) (PreH2 : ((Zlength (l_data)) <= 1000)) (PreH3 : ((Zlength (r_data)) = (Zlength (l_data)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (l_data)))) -> ((0 <= (Znth i l_data 0)) /\ ((Znth i l_data 0) <= (Zlength (l_data)))))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (r_data)))) -> ((0 <= (Znth i_2 r_data 0)) /\ ((Znth i_2 r_data 0) <= (Zlength (l_data)))))) (PreH6 : (n_pre = (Zlength (l_data)))) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.undef_full a_pre n_pre )
|--
  EX (prefix: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data 0 prefix ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 0 prefix )
  **  (IntArray.undef_seg a_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (PreH1 : (1 <= (Zlength (l_data)))) (PreH2 : ((Zlength (l_data)) <= 1000)) (PreH3 : ((Zlength (r_data)) = (Zlength (l_data)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (l_data)))) -> ((0 <= (Znth i l_data 0)) /\ ((Znth i l_data 0) <= (Zlength (l_data)))))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (r_data)))) -> ((0 <= (Znth i_2 r_data 0)) /\ ((Znth i_2 r_data 0) <= (Zlength (l_data)))))) (PreH6 : (n_pre = (Zlength (l_data)))) ,
  TT && emp 
|--
  “ (CandyCandidatePrefix n_pre l_data r_data 0 (@nil Z) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (PreH1 : (1 <= (Zlength (l_data)))) (PreH2 : ((Zlength (l_data)) <= 1000)) (PreH3 : ((Zlength (r_data)) = (Zlength (l_data)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (l_data)))) -> ((0 <= (Znth i l_data 0)) /\ ((Znth i l_data 0) <= (Zlength (l_data)))))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (r_data)))) -> ((0 <= (Znth i_2 r_data 0)) /\ ((Znth i_2 r_data 0) <= (Zlength (l_data)))))) (PreH6 : (n_pre = (Zlength (l_data)))) ,
  (CandyCandidatePrefix n_pre l_data r_data 0 (@nil Z) )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (PreH1 : (1 <= (Zlength (l_data)))) (PreH2 : ((Zlength (l_data)) <= 1000)) (PreH3 : ((Zlength (r_data)) = (Zlength (l_data)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (l_data)))) -> ((0 <= (Znth i l_data 0)) /\ ((Znth i l_data 0) <= (Zlength (l_data)))))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (r_data)))) -> ((0 <= (Znth i_2 r_data 0)) /\ ((Znth i_2 r_data 0) <= (Zlength (l_data)))))) (PreH6 : (n_pre = (Zlength (l_data)))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (PreH1 : (1 <= (Zlength (l_data)))) (PreH2 : ((Zlength (l_data)) <= 1000)) (PreH3 : ((Zlength (r_data)) = (Zlength (l_data)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (l_data)))) -> ((0 <= (Znth i l_data 0)) /\ ((Znth i l_data 0) <= (Zlength (l_data)))))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (r_data)))) -> ((0 <= (Znth i_2 r_data 0)) /\ ((Znth i_2 r_data 0) <= (Zlength (l_data)))))) (PreH6 : (n_pre = (Zlength (l_data)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))
.

Definition solver_entail_wit_2 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix_2 )) ,
  (IntArray.seg a_pre 0 (i + 1 ) (app (prefix_2) ((cons (((n_pre - (Znth i l_data 0) ) - (Znth i r_data 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
|--
  EX (prefix: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data (i + 1 ) prefix ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 (i + 1 ) prefix )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix_2 )) ,
  TT && emp 
|--
  “ (CandyCandidatePrefix n_pre l_data r_data (i + 1 ) (app (prefix_2) ((cons (((n_pre - (Znth i l_data 0) ) - (Znth i r_data 0) )) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix_2 )) ,
  (CandyCandidatePrefix n_pre l_data r_data (i + 1 ) (app (prefix_2) ((cons (((n_pre - (Znth i l_data 0) ) - (Znth i r_data 0) )) ((@nil Z))))) )
.

Definition solver_entail_wit_3 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate 0 ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (a_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.seg a_pre 0 i prefix )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate 0 ) ”
  &&  (IntArray.full a_pre n_pre candidate )
).

Definition solver_entail_wit_4 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate_2 i )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate_2 )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i 0 0 ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate_2 i )) ,
  TT && emp 
|--
  “ (CandyLeftCount candidate_2 i 0 0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate_2 i )) ,
  (CandyLeftCount candidate_2 i 0 0 )
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate_2 i )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate_2 i )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))
.

Definition solver_entail_wit_5_1 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) <= (Znth i candidate_2 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH18 : (CandyLeftCount candidate_2 i j cl )) ,
  (IntArray.full a_pre n_pre candidate_2 )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (0 <= (cl + 0 )) ” 
  &&  “ ((cl + 0 ) <= (j + 1 )) ” 
  &&  “ (cr = 0) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i (j + 1 ) (cl + 0 ) ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) <= (Znth i candidate_2 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH18 : (CandyLeftCount candidate_2 i j cl )) ,
  TT && emp 
|--
  “ (CandyLeftCount candidate_2 i (j + 1 ) (cl + 0 ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) <= (Znth i candidate_2 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH18 : (CandyLeftCount candidate_2 i j cl )) ,
  (CandyLeftCount candidate_2 i (j + 1 ) (cl + 0 ) )
.

Definition solver_entail_wit_5_2 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) > (Znth i candidate_2 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH18 : (CandyLeftCount candidate_2 i j cl )) ,
  (IntArray.full a_pre n_pre candidate_2 )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (0 <= (cl + 1 )) ” 
  &&  “ ((cl + 1 ) <= (j + 1 )) ” 
  &&  “ (cr = 0) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i (j + 1 ) (cl + 1 ) ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) > (Znth i candidate_2 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH18 : (CandyLeftCount candidate_2 i j cl )) ,
  TT && emp 
|--
  “ (CandyLeftCount candidate_2 i (j + 1 ) (cl + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) > (Znth i candidate_2 0))) (PreH2 : (j < i)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= i)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= j)) (PreH16 : (cr = 0)) (PreH17 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH18 : (CandyLeftCount candidate_2 i j cl )) ,
  (CandyLeftCount candidate_2 i (j + 1 ) (cl + 1 ) )
.

Definition solver_entail_wit_6 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH17 : (CandyLeftCount candidate_2 i j cl )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate_2 )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= cr) ” 
  &&  “ (cr <= ((i + 1 ) - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i (i + 1 ) cr ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH17 : (CandyLeftCount candidate_2 i j cl )) ,
  TT && emp 
|--
  “ (CandyRightCount candidate_2 i (i + 1 ) 0 ) ” 
  &&  “ (CandyLeftCount candidate_2 i i cl ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH17 : (CandyLeftCount candidate_2 i j cl )) ,
  (CandyRightCount candidate_2 i (i + 1 ) 0 )
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH17 : (CandyLeftCount candidate_2 i j cl )) ,
  (CandyLeftCount candidate_2 i i cl )
.

Definition solver_entail_wit_6_split_goal_3 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH17 : (CandyLeftCount candidate_2 i j cl )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))
.

Definition solver_entail_wit_6_split_goal_4 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (j >= i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH17 : (CandyLeftCount candidate_2 i j cl )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))
.

Definition solver_entail_wit_7_1 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) <= (Znth i candidate_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH19 : (CandyLeftCount candidate_2 i i cl )) (PreH20 : (CandyRightCount candidate_2 i j cr )) ,
  (IntArray.full a_pre n_pre candidate_2 )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= (cr + 0 )) ” 
  &&  “ ((cr + 0 ) <= ((j + 1 ) - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i (j + 1 ) (cr + 0 ) ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) <= (Znth i candidate_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH19 : (CandyLeftCount candidate_2 i i cl )) (PreH20 : (CandyRightCount candidate_2 i j cr )) ,
  TT && emp 
|--
  “ (CandyRightCount candidate_2 i (j + 1 ) (cr + 0 ) ) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) <= (Znth i candidate_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH19 : (CandyLeftCount candidate_2 i i cl )) (PreH20 : (CandyRightCount candidate_2 i j cr )) ,
  (CandyRightCount candidate_2 i (j + 1 ) (cr + 0 ) )
.

Definition solver_entail_wit_7_2 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) > (Znth i candidate_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH19 : (CandyLeftCount candidate_2 i i cl )) (PreH20 : (CandyRightCount candidate_2 i j cr )) ,
  (IntArray.full a_pre n_pre candidate_2 )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= (cr + 1 )) ” 
  &&  “ ((cr + 1 ) <= ((j + 1 ) - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i (j + 1 ) (cr + 1 ) ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) > (Znth i candidate_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH19 : (CandyLeftCount candidate_2 i i cl )) (PreH20 : (CandyRightCount candidate_2 i j cr )) ,
  TT && emp 
|--
  “ (CandyRightCount candidate_2 i (j + 1 ) (cr + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : ((Znth j candidate_2 0) > (Znth i candidate_2 0))) (PreH2 : (j < n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH19 : (CandyLeftCount candidate_2 i i cl )) (PreH20 : (CandyRightCount candidate_2 i j cr )) ,
  (CandyRightCount candidate_2 i (j + 1 ) (cr + 1 ) )
.

Definition solver_entail_wit_8 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (cr = (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate_2 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH21 : (CandyLeftCount candidate_2 i i cl )) (PreH22 : (CandyRightCount candidate_2 i j cr )) ,
  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate_2 )
|--
  EX (candidate: (@list Z)) ,
  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate (i + 1 ) ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (cr = (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate_2 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH21 : (CandyLeftCount candidate_2 i i cl )) (PreH22 : (CandyRightCount candidate_2 i j cr )) ,
  TT && emp 
|--
  “ (CandyCheckedPrefix l_data r_data candidate_2 (i + 1 ) ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (cr = (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate_2 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH21 : (CandyLeftCount candidate_2 i i cl )) (PreH22 : (CandyRightCount candidate_2 i j cr )) ,
  (CandyCheckedPrefix l_data r_data candidate_2 (i + 1 ) )
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (cr = (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate_2 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH21 : (CandyLeftCount candidate_2 i i cl )) (PreH22 : (CandyRightCount candidate_2 i j cr )) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate_2: (@list Z)) (PreH1 : (cr = (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate_2 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 l_data 0)) /\ ((Znth k_3 l_data 0) <= n_pre)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 r_data 0)) /\ ((Znth k_4 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate_2 )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate_2 i )) (PreH21 : (CandyLeftCount candidate_2 i i cl )) (PreH22 : (CandyRightCount candidate_2 i j cr )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))
.

Definition solver_return_wit_1 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate i )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  EX (result: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (Spec l_data r_data (Some (result)) ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre result )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate i )) ,
  TT && emp 
|--
  “ (Spec l_data r_data (Some (candidate)) ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (i: Z) (candidate: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (CandyCheckedPrefix l_data r_data candidate i )) ,
  (Spec l_data r_data (Some (candidate)) )
.

Definition solver_return_wit_2 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cl <> (Znth i l_data 0))) (PreH2 : ((Znth i candidate 0) >= 1)) (PreH3 : (j >= n_pre)) (PreH4 : (n_pre = (Zlength (l_data)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (r_data)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 <= cl)) (PreH16 : (cl <= i)) (PreH17 : (0 <= cr)) (PreH18 : (cr <= (j - (i + 1 ) ))) (PreH19 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH20 : (CandyLeftCount candidate i i cl )) (PreH21 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
  **  (IntArray.full r_pre n_pre r_data )
|--
  EX (post: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (Spec l_data r_data None ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre post )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cl <> (Znth i l_data 0))) (PreH2 : ((Znth i candidate 0) >= 1)) (PreH3 : (j >= n_pre)) (PreH4 : (n_pre = (Zlength (l_data)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (r_data)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 <= cl)) (PreH16 : (cl <= i)) (PreH17 : (0 <= cr)) (PreH18 : (cr <= (j - (i + 1 ) ))) (PreH19 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH20 : (CandyLeftCount candidate i i cl )) (PreH21 : (CandyRightCount candidate i j cr )) ,
  TT && emp 
|--
  “ (Spec l_data r_data None ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cl <> (Znth i l_data 0))) (PreH2 : ((Znth i candidate 0) >= 1)) (PreH3 : (j >= n_pre)) (PreH4 : (n_pre = (Zlength (l_data)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (r_data)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 <= cl)) (PreH16 : (cl <= i)) (PreH17 : (0 <= cr)) (PreH18 : (cr <= (j - (i + 1 ) ))) (PreH19 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH20 : (CandyLeftCount candidate i i cl )) (PreH21 : (CandyRightCount candidate i j cr )) ,
  (Spec l_data r_data None )
.

Definition solver_return_wit_3 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth i candidate 0) < 1)) (PreH2 : (j >= n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  EX (post: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (Spec l_data r_data None ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre post )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth i candidate 0) < 1)) (PreH2 : (j >= n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  TT && emp 
|--
  “ (Spec l_data r_data None ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth i candidate 0) < 1)) (PreH2 : (j >= n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (Spec l_data r_data None )
.

Definition solver_return_wit_4 := 
(
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cr <> (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH21 : (CandyLeftCount candidate i i cl )) (PreH22 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  EX (post: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (Spec l_data r_data None ) ”
  &&  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre post )
) \/
(
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cr <> (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH21 : (CandyLeftCount candidate i i cl )) (PreH22 : (CandyRightCount candidate i j cr )) ,
  TT && emp 
|--
  “ (Spec l_data r_data None ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 := 
forall (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cr <> (Znth i r_data 0))) (PreH2 : (cl = (Znth i l_data 0))) (PreH3 : ((Znth i candidate 0) >= 1)) (PreH4 : (j >= n_pre)) (PreH5 : (n_pre = (Zlength (l_data)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (r_data)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH11 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((i + 1 ) <= j)) (PreH15 : (j <= n_pre)) (PreH16 : (0 <= cl)) (PreH17 : (cl <= i)) (PreH18 : (0 <= cr)) (PreH19 : (cr <= (j - (i + 1 ) ))) (PreH20 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH21 : (CandyLeftCount candidate i i cl )) (PreH22 : (CandyRightCount candidate i j cr )) ,
  (Spec l_data r_data None )
.

Definition solver_partial_solve_wit_1 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data i prefix ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l_data 0))
  **  (IntArray.missing_i l_pre i 0 n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
.

Definition solver_partial_solve_wit_2 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data i prefix ) ”
  &&  (((r_pre + (i * sizeof(INT)))) # Int  |-> (Znth i r_data 0))
  **  (IntArray.missing_i r_pre i 0 n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
.

Definition solver_partial_solve_wit_3 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (prefix: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data i prefix )) ,
  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.seg a_pre 0 i prefix )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data i prefix ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.seg a_pre 0 i prefix )
.

Definition solver_partial_solve_wit_4 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j < i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH17 : (CandyLeftCount candidate i j cl )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (j < i) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= j) ” 
  &&  “ (cr = 0) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i j cl ) ”
  &&  (((a_pre + (j * sizeof(INT)))) # Int  |-> (Znth j candidate 0))
  **  (IntArray.missing_i a_pre j 0 n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
.

Definition solver_partial_solve_wit_5 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j < i)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j <= i)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= j)) (PreH15 : (cr = 0)) (PreH16 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH17 : (CandyLeftCount candidate i j cl )) ,
  (IntArray.full a_pre n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ (j < i) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= j) ” 
  &&  “ (cr = 0) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i j cl ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i candidate 0))
  **  (IntArray.missing_i a_pre i 0 n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
.

Definition solver_partial_solve_wit_6 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= i)) (PreH15 : (0 <= cr)) (PreH16 : (cr <= (j - (i + 1 ) ))) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i i cl )) (PreH19 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (j < n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= cr) ” 
  &&  “ (cr <= (j - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i j cr ) ”
  &&  (((a_pre + (j * sizeof(INT)))) # Int  |-> (Znth j candidate 0))
  **  (IntArray.missing_i a_pre j 0 n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
.

Definition solver_partial_solve_wit_7 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j < n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= i)) (PreH15 : (0 <= cr)) (PreH16 : (cr <= (j - (i + 1 ) ))) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i i cl )) (PreH19 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ (j < n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= cr) ” 
  &&  “ (cr <= (j - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i j cr ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i candidate 0))
  **  (IntArray.missing_i a_pre i 0 n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
.

Definition solver_partial_solve_wit_8 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (j >= n_pre)) (PreH2 : (n_pre = (Zlength (l_data)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (r_data)) = n_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH8 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((i + 1 ) <= j)) (PreH12 : (j <= n_pre)) (PreH13 : (0 <= cl)) (PreH14 : (cl <= i)) (PreH15 : (0 <= cr)) (PreH16 : (cr <= (j - (i + 1 ) ))) (PreH17 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH18 : (CandyLeftCount candidate i i cl )) (PreH19 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
  **  (IntArray.full a_pre n_pre candidate )
|--
  “ (j >= n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= cr) ” 
  &&  “ (cr <= (j - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i j cr ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i candidate 0))
  **  (IntArray.missing_i a_pre i 0 n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
.

Definition solver_partial_solve_wit_9 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : ((Znth i candidate 0) >= 1)) (PreH2 : (j >= n_pre)) (PreH3 : (n_pre = (Zlength (l_data)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (r_data)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH9 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((i + 1 ) <= j)) (PreH13 : (j <= n_pre)) (PreH14 : (0 <= cl)) (PreH15 : (cl <= i)) (PreH16 : (0 <= cr)) (PreH17 : (cr <= (j - (i + 1 ) ))) (PreH18 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH19 : (CandyLeftCount candidate i i cl )) (PreH20 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full a_pre n_pre candidate )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ ((Znth i candidate 0) >= 1) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= cr) ” 
  &&  “ (cr <= (j - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i j cr ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l_data 0))
  **  (IntArray.missing_i l_pre i 0 n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
  **  (IntArray.full r_pre n_pre r_data )
.

Definition solver_partial_solve_wit_10 := 
forall (a_pre: Z) (r_pre: Z) (l_pre: Z) (n_pre: Z) (r_data: (@list Z)) (l_data: (@list Z)) (cr: Z) (cl: Z) (j: Z) (i: Z) (candidate: (@list Z)) (PreH1 : (cl = (Znth i l_data 0))) (PreH2 : ((Znth i candidate 0) >= 1)) (PreH3 : (j >= n_pre)) (PreH4 : (n_pre = (Zlength (l_data)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (r_data)) = n_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre)))) (PreH10 : (CandyCandidatePrefix n_pre l_data r_data n_pre candidate )) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((i + 1 ) <= j)) (PreH14 : (j <= n_pre)) (PreH15 : (0 <= cl)) (PreH16 : (cl <= i)) (PreH17 : (0 <= cr)) (PreH18 : (cr <= (j - (i + 1 ) ))) (PreH19 : (CandyCheckedPrefix l_data r_data candidate i )) (PreH20 : (CandyLeftCount candidate i i cl )) (PreH21 : (CandyRightCount candidate i j cr )) ,
  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
  **  (IntArray.full r_pre n_pre r_data )
|--
  “ (cl = (Znth i l_data 0)) ” 
  &&  “ ((Znth i candidate 0) >= 1) ” 
  &&  “ (j >= n_pre) ” 
  &&  “ (n_pre = (Zlength (l_data))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (r_data)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l_data 0)) /\ ((Znth k l_data 0) <= n_pre))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 r_data 0)) /\ ((Znth k_2 r_data 0) <= n_pre))) ” 
  &&  “ (CandyCandidatePrefix n_pre l_data r_data n_pre candidate ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= i) ” 
  &&  “ (0 <= cr) ” 
  &&  “ (cr <= (j - (i + 1 ) )) ” 
  &&  “ (CandyCheckedPrefix l_data r_data candidate i ) ” 
  &&  “ (CandyLeftCount candidate i i cl ) ” 
  &&  “ (CandyRightCount candidate i j cr ) ”
  &&  (((r_pre + (i * sizeof(INT)))) # Int  |-> (Znth i r_data 0))
  **  (IntArray.missing_i r_pre i 0 n_pre r_data )
  **  (IntArray.full l_pre n_pre l_data )
  **  (IntArray.full a_pre n_pre candidate )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
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

End VC_Correct.
