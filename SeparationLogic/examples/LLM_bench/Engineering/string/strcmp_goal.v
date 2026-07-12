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
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function strcmp -----*)

Definition strcmp_safety_wit_1 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (valid_string str1 )) (PreH2 : (valid_string str2 )) (PreH3 : ((string_length (str1)) < INT_MAX)) (PreH4 : ((string_length (str2)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcmp_safety_wit_2 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (valid_string str1 )) (PreH2 : (valid_string str2 )) (PreH3 : ((string_length (str1)) < INT_MAX)) (PreH4 : ((string_length (str2)) < INT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (str1)))) (PreH7 : (i <= (string_length (str2)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strcmp_safety_wit_3 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str1)))) (PreH9 : (i <= (string_length (str2)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strcmp_safety_wit_4 := 
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str1)))) (PreH9 : (i <= (string_length (str2)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
) \/
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str1)))) (PreH9 : (i <= (string_length (str2)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
).

Definition strcmp_safety_wit_4_split_goal_1 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str1)))) (PreH9 : (i <= (string_length (str2)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ”
.

Definition strcmp_safety_wit_4_split_goal_2 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str1)))) (PreH9 : (i <= (string_length (str2)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strcmp_safety_wit_5 := 
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = 0)) (PreH2 : (valid_string str1 )) (PreH3 : (valid_string str2 )) (PreH4 : ((string_length (str1)) < INT_MAX)) (PreH5 : ((string_length (str2)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (str1)))) (PreH8 : (i <= (string_length (str2)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
) \/
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = 0)) (PreH2 : (valid_string str1 )) (PreH3 : (valid_string str2 )) (PreH4 : ((string_length (str1)) < INT_MAX)) (PreH5 : ((string_length (str2)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (str1)))) (PreH8 : (i <= (string_length (str2)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
).

Definition strcmp_safety_wit_5_split_goal_1 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = 0)) (PreH2 : (valid_string str1 )) (PreH3 : (valid_string str2 )) (PreH4 : ((string_length (str1)) < INT_MAX)) (PreH5 : ((string_length (str2)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (str1)))) (PreH8 : (i <= (string_length (str2)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ”
.

Definition strcmp_safety_wit_5_split_goal_2 := 
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = 0)) (PreH2 : (valid_string str1 )) (PreH3 : (valid_string str2 )) (PreH4 : ((string_length (str1)) < INT_MAX)) (PreH5 : ((string_length (str2)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (str1)))) (PreH8 : (i <= (string_length (str2)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strcmp_entail_wit_1 := 
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (valid_string str1 )) (PreH2 : (valid_string str2 )) (PreH3 : ((string_length (str1)) < INT_MAX)) (PreH4 : ((string_length (str2)) < INT_MAX)) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (str1))) ” 
  &&  “ (0 <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (string_length (str2))) ” 
  &&  “ (0 <= (string_length (str1))) ”
  &&  emp
).

Definition strcmp_entail_wit_1_split_goal_1 := 
forall (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) ,
  (0 <= (string_length (str2)))
.

Definition strcmp_entail_wit_1_split_goal_2 := 
forall (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) ,
  (0 <= (string_length (str1)))
.

Definition strcmp_entail_wit_2 := 
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str1)))) (PreH9 : (i <= (string_length (str2)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (str1))) ” 
  &&  “ ((i + 1 ) <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (string_length (str1)))) (PreH11 : (i <= (string_length (str2)))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  TT && emp 
|--
  “ (((Znth (0) ((c_string (str1))) (0)) = (Znth (0) ((c_string (str2))) (0))) /\ ((Znth (((i + 1 ) - 1 )) ((c_string (str1))) (0)) = (Znth (((i + 1 ) - 1 )) ((c_string (str2))) (0)))) ” 
  &&  “ ((i + 1 ) <= (string_length (str2))) ” 
  &&  “ ((i + 1 ) <= (string_length (str1))) ”
  &&  emp
).

Definition strcmp_entail_wit_2_split_goal_1 := 
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (string_length (str1)))) (PreH11 : (i <= (string_length (str2)))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (((Znth (0) ((c_string (str1))) (0)) = (Znth (0) ((c_string (str2))) (0))) /\ ((Znth (((i + 1 ) - 1 )) ((c_string (str1))) (0)) = (Znth (((i + 1 ) - 1 )) ((c_string (str2))) (0))))
.

Definition strcmp_entail_wit_2_split_goal_2 := 
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (string_length (str1)))) (PreH11 : (i <= (string_length (str2)))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((i + 1 ) <= (string_length (str2)))
.

Definition strcmp_entail_wit_2_split_goal_3 := 
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (string_length (str1)))) (PreH11 : (i <= (string_length (str2)))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((i + 1 ) <= (string_length (str1)))
.

Definition strcmp_return_wit_1 := 
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = 0)) (PreH2 : (valid_string str1 )) (PreH3 : (valid_string str2 )) (PreH4 : ((string_length (str1)) < INT_MAX)) (PreH5 : ((string_length (str2)) < INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (str1)))) (PreH8 : (i <= (string_length (str2)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = 0)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : ((string_length (str1)) < INT_MAX)) (PreH7 : ((string_length (str2)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= (string_length (str1)))) (PreH10 : (i <= (string_length (str2)))) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  TT && emp 
|--
  “ (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  emp
).

Definition strcmp_return_wit_1_split_goal_1 := 
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = 0)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : ((string_length (str1)) < INT_MAX)) (PreH7 : ((string_length (str2)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= (string_length (str1)))) (PreH10 : (i <= (string_length (str2)))) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) )
.

Definition strcmp_return_wit_2 := 
(
forall (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (str1)))) (PreH9 : (i <= (string_length (str2)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (string_length (str1)))) (PreH11 : (i <= (string_length (str2)))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  TT && emp 
|--
  “ (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  emp
).

Definition strcmp_return_wit_2_split_goal_1 := 
forall (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= (string_length (str1)))) (PreH11 : (i <= (string_length (str2)))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (strcmp_result str1 str2 ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) )
.

(*----- Function strncmp -----*)

Definition strncmp_safety_wit_1 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (valid_string str1 )) (PreH2 : (valid_string str2 )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncmp_safety_wit_2 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (valid_string str1 )) (PreH3 : (valid_string str2 )) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : ((string_length (str1)) < INT_MAX)) (PreH7 : ((string_length (str2)) < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (i <= (string_length (str1)))) (PreH11 : (i <= (string_length (str2)))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncmp_safety_wit_3 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition strncmp_safety_wit_4 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ False ”
.

Definition strncmp_safety_wit_5 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (i <= (string_length (str1)))) (PreH12 : (i <= (string_length (str2)))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ False ”
.

Definition strncmp_safety_wit_6 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH3 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ False ”
.

Definition strncmp_safety_wit_7 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (i <= (string_length (str1)))) (PreH12 : (i <= (string_length (str2)))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strncmp_safety_wit_8 := 
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH3 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
) \/
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH3 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
).

Definition strncmp_safety_wit_8_split_goal_1 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH3 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ”
.

Definition strncmp_safety_wit_8_split_goal_2 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH3 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strncmp_safety_wit_9 := 
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
) \/
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
).

Definition strncmp_safety_wit_9_split_goal_1 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) <= INT_MAX) ”
.

Definition strncmp_safety_wit_9_split_goal_2 := 
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s2" ) )) # Ptr  |-> s2_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ ((INT_MIN) <= ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) )) ”
.

Definition strncmp_entail_wit_1 := 
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (valid_string str1 )) (PreH2 : (valid_string str2 )) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : ((string_length (str1)) < INT_MAX)) (PreH6 : ((string_length (str2)) < INT_MAX)) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= (string_length (str1))) ” 
  &&  “ (0 <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (string_length (str2))) ” 
  &&  “ (0 <= (string_length (str1))) ”
  &&  emp
).

Definition strncmp_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) ,
  (0 <= (string_length (str2)))
.

Definition strncmp_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) ,
  (0 <= (string_length (str1)))
.

Definition strncmp_entail_wit_2 := 
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH2 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (valid_string str1 ) ” 
  &&  “ (valid_string str2 ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((string_length (str1)) < INT_MAX) ” 
  &&  “ ((string_length (str2)) < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((i + 1 ) <= (string_length (str1))) ” 
  &&  “ ((i + 1 ) <= (string_length (str2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0)))) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (valid_string str1 )) (PreH7 : (valid_string str2 )) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((string_length (str1)) < INT_MAX)) (PreH11 : ((string_length (str2)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (i <= (string_length (str1)))) (PreH15 : (i <= (string_length (str2)))) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  TT && emp 
|--
  “ (((Znth (0) ((c_string (str1))) (0)) = (Znth (0) ((c_string (str2))) (0))) /\ ((Znth (((i + 1 ) - 1 )) ((c_string (str1))) (0)) = (Znth (((i + 1 ) - 1 )) ((c_string (str2))) (0)))) ” 
  &&  “ ((i + 1 ) <= (string_length (str2))) ” 
  &&  “ ((i + 1 ) <= (string_length (str1))) ”
  &&  emp
).

Definition strncmp_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (valid_string str1 )) (PreH7 : (valid_string str2 )) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((string_length (str1)) < INT_MAX)) (PreH11 : ((string_length (str2)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (i <= (string_length (str1)))) (PreH15 : (i <= (string_length (str2)))) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (((Znth (0) ((c_string (str1))) (0)) = (Znth (0) ((c_string (str2))) (0))) /\ ((Znth (((i + 1 ) - 1 )) ((c_string (str1))) (0)) = (Znth (((i + 1 ) - 1 )) ((c_string (str2))) (0))))
.

Definition strncmp_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (valid_string str1 )) (PreH7 : (valid_string str2 )) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((string_length (str1)) < INT_MAX)) (PreH11 : ((string_length (str2)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (i <= (string_length (str1)))) (PreH15 : (i <= (string_length (str2)))) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((i + 1 ) <= (string_length (str2)))
.

Definition strncmp_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : ((Znth i (c_string (str1)) 0) = (Znth i (c_string (str2)) 0))) (PreH4 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH5 : (i < n_pre)) (PreH6 : (valid_string str1 )) (PreH7 : (valid_string str2 )) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((string_length (str1)) < INT_MAX)) (PreH11 : ((string_length (str2)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (i <= (string_length (str1)))) (PreH15 : (i <= (string_length (str2)))) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  ((i + 1 ) <= (string_length (str1)))
.

Definition strncmp_return_wit_1 := 
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) = 0)) (PreH3 : (i < n_pre)) (PreH4 : (valid_string str1 )) (PreH5 : (valid_string str2 )) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : ((string_length (str1)) < INT_MAX)) (PreH9 : ((string_length (str2)) < INT_MAX)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (i <= (string_length (str1)))) (PreH13 : (i <= (string_length (str2)))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (i <> n_pre)) (PreH4 : ((Znth i (c_string (str1)) 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (valid_string str1 )) (PreH7 : (valid_string str2 )) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((string_length (str1)) < INT_MAX)) (PreH11 : ((string_length (str2)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (i <= (string_length (str1)))) (PreH15 : (i <= (string_length (str2)))) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  TT && emp 
|--
  “ (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  emp
).

Definition strncmp_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (i <> n_pre)) (PreH4 : ((Znth i (c_string (str1)) 0) = 0)) (PreH5 : (i < n_pre)) (PreH6 : (valid_string str1 )) (PreH7 : (valid_string str2 )) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : ((string_length (str1)) < INT_MAX)) (PreH11 : ((string_length (str2)) < INT_MAX)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (i <= (string_length (str1)))) (PreH15 : (i <= (string_length (str2)))) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) )
.

Definition strncmp_return_wit_2 := 
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i <> n_pre)) (PreH2 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH3 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH4 : (i < n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (i <> n_pre)) (PreH4 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH5 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (valid_string str1 )) (PreH8 : (valid_string str2 )) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((string_length (str1)) < INT_MAX)) (PreH12 : ((string_length (str2)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (i <= (string_length (str1)))) (PreH16 : (i <= (string_length (str2)))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  TT && emp 
|--
  “ (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) ) ”
  &&  emp
).

Definition strncmp_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (i <> n_pre)) (PreH4 : ((Znth i (c_string (str1)) 0) <> (Znth i (c_string (str2)) 0))) (PreH5 : ((Znth i (c_string (str1)) 0) <> 0)) (PreH6 : (i < n_pre)) (PreH7 : (valid_string str1 )) (PreH8 : (valid_string str2 )) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) (PreH11 : ((string_length (str1)) < INT_MAX)) (PreH12 : ((string_length (str2)) < INT_MAX)) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (i <= (string_length (str1)))) (PreH16 : (i <= (string_length (str2)))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (strncmp_result str1 str2 n_pre ((Znth i (c_string (str1)) 0) - (Znth i (c_string (str2)) 0) ) )
.

Definition strncmp_return_wit_3 := 
(
forall (n_pre: Z) (s2_pre: Z) (s1_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (i = n_pre)) (PreH2 : (i >= n_pre)) (PreH3 : (valid_string str1 )) (PreH4 : (valid_string str2 )) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : ((string_length (str1)) < INT_MAX)) (PreH8 : ((string_length (str2)) < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (i <= (string_length (str1)))) (PreH12 : (i <= (string_length (str2)))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
|--
  “ (strncmp_result str1 str2 n_pre 0 ) ”
  &&  (store_string s1_pre str1 )
  **  (store_string s2_pre str2 )
) \/
(
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (i = n_pre)) (PreH4 : (i >= n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  TT && emp 
|--
  “ (strncmp_result str1 str2 n_pre 0 ) ”
  &&  emp
).

Definition strncmp_return_wit_3_split_goal_1 := 
forall (n_pre: Z) (str2: (@list Z)) (str1: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (str2)) + 1 ))) (PreH2 : (0 <= ((string_length (str1)) + 1 ))) (PreH3 : (i = n_pre)) (PreH4 : (i >= n_pre)) (PreH5 : (valid_string str1 )) (PreH6 : (valid_string str2 )) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : ((string_length (str1)) < INT_MAX)) (PreH10 : ((string_length (str2)) < INT_MAX)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (i <= (string_length (str1)))) (PreH14 : (i <= (string_length (str2)))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) ((c_string (str1))) (0)) = (Znth (k) ((c_string (str2))) (0))))) ,
  (strncmp_result str1 str2 n_pre 0 )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_strcmp_safety_wit_1 : strcmp_safety_wit_1.
Axiom proof_of_strcmp_safety_wit_2 : strcmp_safety_wit_2.
Axiom proof_of_strcmp_safety_wit_3 : strcmp_safety_wit_3.
Axiom proof_of_strcmp_safety_wit_4 : strcmp_safety_wit_4.
Axiom proof_of_strcmp_safety_wit_5 : strcmp_safety_wit_5.
Axiom proof_of_strcmp_entail_wit_1 : strcmp_entail_wit_1.
Axiom proof_of_strcmp_entail_wit_2 : strcmp_entail_wit_2.
Axiom proof_of_strcmp_return_wit_1 : strcmp_return_wit_1.
Axiom proof_of_strcmp_return_wit_2 : strcmp_return_wit_2.
Axiom proof_of_strncmp_safety_wit_1 : strncmp_safety_wit_1.
Axiom proof_of_strncmp_safety_wit_2 : strncmp_safety_wit_2.
Axiom proof_of_strncmp_safety_wit_3 : strncmp_safety_wit_3.
Axiom proof_of_strncmp_safety_wit_4 : strncmp_safety_wit_4.
Axiom proof_of_strncmp_safety_wit_5 : strncmp_safety_wit_5.
Axiom proof_of_strncmp_safety_wit_6 : strncmp_safety_wit_6.
Axiom proof_of_strncmp_safety_wit_7 : strncmp_safety_wit_7.
Axiom proof_of_strncmp_safety_wit_8 : strncmp_safety_wit_8.
Axiom proof_of_strncmp_safety_wit_9 : strncmp_safety_wit_9.
Axiom proof_of_strncmp_entail_wit_1 : strncmp_entail_wit_1.
Axiom proof_of_strncmp_entail_wit_2 : strncmp_entail_wit_2.
Axiom proof_of_strncmp_return_wit_1 : strncmp_return_wit_1.
Axiom proof_of_strncmp_return_wit_2 : strncmp_return_wit_2.
Axiom proof_of_strncmp_return_wit_3 : strncmp_return_wit_3.

End VC_Correct.
