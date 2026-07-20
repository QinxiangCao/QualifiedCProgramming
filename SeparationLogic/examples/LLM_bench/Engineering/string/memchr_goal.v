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

(*----- Function memchr -----*)

Definition memchr_safety_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memchr_safety_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : ((Znth i bytes 0) <> c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  (CharArray.full s_pre n_pre bytes )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memchr_safety_wit_3 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memchr_entail_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (CharArray.full s_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (c_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  emp
).

Definition memchr_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (bytes: (@list Z)) (PreH1 : (all_ascii bytes )) (PreH2 : ((Zlength (bytes)) = n_pre)) (PreH3 : (0 <= c_pre)) (PreH4 : (c_pre <= 127)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (bytes) (0)) <> c_pre))
.

Definition memchr_entail_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : ((Znth i bytes 0) <> c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  (CharArray.full s_pre n_pre bytes )
|--
  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (CharArray.full s_pre n_pre bytes )
.

Definition memchr_return_wit_1 := 
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  (CharArray.full s_pre n_pre bytes )
|--
  “ (memchr_result bytes c_pre n_pre 0 s_pre ) ”
  &&  (CharArray.full s_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  TT && emp 
|--
  “ (memchr_result bytes c_pre n_pre 0 s_pre ) ”
  &&  emp
).

Definition memchr_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  (memchr_result bytes c_pre n_pre 0 s_pre )
.

Definition memchr_return_wit_2 := 
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : ((Znth i bytes 0) = c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  (CharArray.full s_pre n_pre bytes )
|--
  “ (memchr_result bytes c_pre n_pre (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  (CharArray.full s_pre n_pre bytes )
) \/
(
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : ((Znth i bytes 0) = c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  TT && emp 
|--
  “ (memchr_result bytes c_pre n_pre (s_pre + (i * sizeof(CHAR))) s_pre ) ”
  &&  emp
).

Definition memchr_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : ((Znth i bytes 0) = c_pre)) (PreH2 : (i < n_pre)) (PreH3 : (all_ascii bytes )) (PreH4 : ((Zlength (bytes)) = n_pre)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 127)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  (memchr_result bytes c_pre n_pre (s_pre + (i * sizeof(CHAR))) s_pre )
.

Definition memchr_partial_solve_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (s_pre: Z) (bytes: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (all_ascii bytes )) (PreH3 : ((Zlength (bytes)) = n_pre)) (PreH4 : (0 <= c_pre)) (PreH5 : (c_pre <= 127)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre))) ,
  (CharArray.full s_pre n_pre bytes )
|--
  “ (i < n_pre) ” 
  &&  “ (all_ascii bytes ) ” 
  &&  “ ((Zlength (bytes)) = n_pre) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 127) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (bytes) (0)) <> c_pre)) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i bytes 0))
  **  (CharArray.missing_i s_pre i 0 n_pre bytes )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_memchr_safety_wit_1 : memchr_safety_wit_1.
Axiom proof_of_memchr_safety_wit_2 : memchr_safety_wit_2.
Axiom proof_of_memchr_safety_wit_3 : memchr_safety_wit_3.
Axiom proof_of_memchr_entail_wit_1 : memchr_entail_wit_1.
Axiom proof_of_memchr_entail_wit_2 : memchr_entail_wit_2.
Axiom proof_of_memchr_return_wit_1 : memchr_return_wit_1.
Axiom proof_of_memchr_return_wit_2 : memchr_return_wit_2.
Axiom proof_of_memchr_partial_solve_wit_1 : memchr_partial_solve_wit_1.

End VC_Correct.
