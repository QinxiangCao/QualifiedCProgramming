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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "top" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "top" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist (0) (i) (text)) stack )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top > 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top > 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack 0) = (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack) ((cons ((Znth i text 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack) ((cons ((Znth i text 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> top)
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack 0) = (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> (top - 1 ))
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack) ((cons ((Znth i text 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack) ((cons ((Znth i text 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist (0) (i) (text)) stack )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full out_pre (n_pre + 1 ) )
|--
  EX (stack: (@list Z)) ,
  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (0) (text)) stack ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre 0 stack )
  **  (CharArray.undef_seg out_pre 0 (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  TT && emp 
|--
  “ (Spec (sublist (0) (0) (text)) (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (Spec (sublist (0) (0) (text)) (@nil Z) )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (0 = (Zlength ((@nil Z))))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))
.

Definition solver_entail_wit_2_1 := 
(
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack_2 0) = (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack_2 )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  EX (stack: (@list Z)) ,
  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (top - 1 )) ” 
  &&  “ ((top - 1 ) <= (i + 1 )) ” 
  &&  “ ((top - 1 ) = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) ((i + 1 )) (text)) stack ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre (top - 1 ) stack )
  **  (CharArray.undef_seg out_pre (top - 1 ) (n_pre + 1 ) )
) \/
(
forall (out_pre: Z) (n_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack_2 0) = (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  (CharArray.full out_pre top stack_2 )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  EX (stack: (@list Z)) ,
  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (top - 1 )) ” 
  &&  “ ((top - 1 ) <= (i + 1 )) ” 
  &&  “ ((top - 1 ) = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) ((i + 1 )) (text)) stack ) ”
  &&  (CharArray.full out_pre (top - 1 ) stack )
  **  (CharArray.undef_seg out_pre (top - 1 ) (n_pre + 1 ) )
).

Definition solver_entail_wit_2_2 := 
(
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
|--
  EX (stack: (@list Z)) ,
  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (top + 1 )) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ ((top + 1 ) = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) ((i + 1 )) (text)) stack ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre (top + 1 ) stack )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  TT && emp 
|--
  “ (Spec (sublist (0) ((i + 1 )) (text)) (app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))) ) ” 
  &&  “ ((top + 1 ) = (Zlength ((app (stack_2) ((cons ((Znth i text 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  (Spec (sublist (0) ((i + 1 )) (text)) (app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack_2)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  ((top + 1 ) = (Zlength ((app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))))))
.

Definition solver_entail_wit_2_3 := 
(
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack_2 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
|--
  EX (stack: (@list Z)) ,
  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (top + 1 )) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ ((top + 1 ) = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) ((i + 1 )) (text)) stack ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre (top + 1 ) stack )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack_2 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  TT && emp 
|--
  “ (Spec (sublist (0) ((i + 1 )) (text)) (app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))) ) ” 
  &&  “ ((top + 1 ) = (Zlength ((app (stack_2) ((cons ((Znth i text 0)) ((@nil Z)))))))) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack_2 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  (Spec (sublist (0) ((i + 1 )) (text)) (app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (stack_2: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack_2 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack_2)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack_2 )) ,
  ((top + 1 ) = (Zlength ((app (stack_2) ((cons ((Znth i text 0)) ((@nil Z))))))))
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
|--
  EX (out_spec: (@list Z)) ,
  “ (Spec text out_spec ) ” 
  &&  “ (top = (Zlength (out_spec))) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre ((Zlength (out_spec)) + 1 ) (app (out_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (out_spec)) + 1 ) (n_pre + 1 ) )
) \/
(
forall (out_pre: Z) (n_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full out_pre (top + 1 ) (app (stack) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
|--
  EX (out_spec: (@list Z)) ,
  “ (Spec text out_spec ) ” 
  &&  “ (top = (Zlength (out_spec))) ”
  &&  (CharArray.full out_pre ((Zlength (out_spec)) + 1 ) (app (out_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_pre ((Zlength (out_spec)) + 1 ) (n_pre + 1 ) )
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top > 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (top > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (i) (text)) stack ) ”
  &&  (((out_pre + ((top - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (top - 1 ) stack 0))
  **  (CharArray.missing_i out_pre (top - 1 ) 0 top stack )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top > 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full out_pre top stack )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (top > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (i) (text)) stack ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i text 0))
  **  (CharArray.missing_i s_pre i 0 n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (top <= 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (i) (text)) stack ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i text 0))
  **  (CharArray.missing_i s_pre i 0 n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (top <= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= top)) (PreH10 : (top <= i)) (PreH11 : (top = (Zlength (stack)))) (PreH12 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (top <= 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (i) (text)) stack ) ”
  &&  (((out_pre + (top * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ ((Znth (top - 1 ) stack 0) <> (Znth i text 0)) ” 
  &&  “ (top > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (i) (text)) stack ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i text 0))
  **  (CharArray.missing_i s_pre i 0 n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : ((Znth (top - 1 ) stack 0) <> (Znth i text 0))) (PreH2 : (top > 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= top)) (PreH11 : (top <= i)) (PreH12 : (top = (Zlength (stack)))) (PreH13 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ ((Znth (top - 1 ) stack 0) <> (Znth i text 0)) ” 
  &&  “ (top > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (i) (text)) stack ) ”
  &&  (((out_pre + (top * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
.

Definition solver_partial_solve_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (stack: (@list Z)) (top: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (text)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= top)) (PreH9 : (top <= i)) (PreH10 : (top = (Zlength (stack)))) (PreH11 : (Spec (sublist (0) (i) (text)) stack )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
  **  (CharArray.undef_seg out_pre top (n_pre + 1 ) )
|--
  “ (i >= n_pre) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((97 <= (Znth j text 0)) /\ ((Znth j text 0) <= 122))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= top) ” 
  &&  “ (top <= i) ” 
  &&  “ (top = (Zlength (stack))) ” 
  &&  “ (Spec (sublist (0) (i) (text)) stack ) ”
  &&  (((out_pre + (top * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg out_pre (top + 1 ) (n_pre + 1 ) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full out_pre top stack )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
