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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P030_1220C_substring_game_in_the_lesson_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "mn" ) )) # Char  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full win_pre n_pre )
|--
  “ ((122 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (122 + 1 )) ”
.

Definition solver_safety_wit_2 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "mn" ) )) # Char  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full win_pre n_pre )
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition solver_safety_wit_3 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "mn" ) )) # Char  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full win_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "mn" ) )) # Char  |-> (122 + 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full win_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) < mn)) (PreH2 : (mn < (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (1) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "mn" ) )) # Char  |-> mn)
|--
  “ False ”
.

Definition solver_safety_wit_6 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) < mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "mn" ) )) # Char  |-> (Znth k text 0))
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "mn" ) )) # Char  |-> mn)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn < (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (1) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "win" ) )) # Ptr  |-> win_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "mn" ) )) # Char  |-> mn)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.undef_full win_pre n_pre )
|--
  EX (out: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (PrefixMinimum text 0 (122 + 1 ) ) ” 
  &&  “ (SpecPrefix text 0 out ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre 0 out )
  **  (CharArray.undef_seg win_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  TT && emp 
|--
  “ (SpecPrefix text 0 (@nil Z) ) ” 
  &&  “ (PrefixMinimum text 0 (122 + 1 ) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (SpecPrefix text 0 (@nil Z) )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (PrefixMinimum text 0 (122 + 1 ) )
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((97 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 122)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))
.

Definition solver_entail_wit_2_1 := 
(
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) < mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
|--
  EX (out: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (PrefixMinimum text (k + 1 ) (Znth k text 0) ) ” 
  &&  “ (SpecPrefix text (k + 1 ) out ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) out )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) < mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  TT && emp 
|--
  “ (SpecPrefix text (k + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ (PrefixMinimum text (k + 1 ) (Znth k text 0) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) < mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (SpecPrefix text (k + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) )
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) < mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (PrefixMinimum text (k + 1 ) (Znth k text 0) )
.

Definition solver_entail_wit_2_2 := 
(
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
|--
  EX (out: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (PrefixMinimum text (k + 1 ) mn ) ” 
  &&  “ (SpecPrefix text (k + 1 ) out ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) out )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  TT && emp 
|--
  “ (SpecPrefix text (k + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ (PrefixMinimum text (k + 1 ) mn ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (SpecPrefix text (k + 1 ) (app (out_2) ((cons (0) ((@nil Z))))) )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (PrefixMinimum text (k + 1 ) mn )
.

Definition solver_entail_wit_2_3 := 
(
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn < (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out_2) ((cons (1) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
|--
  EX (out: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (PrefixMinimum text (k + 1 ) mn ) ” 
  &&  “ (SpecPrefix text (k + 1 ) out ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) out )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn < (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  TT && emp 
|--
  “ (SpecPrefix text (k + 1 ) (app (out_2) ((cons (1) ((@nil Z))))) ) ” 
  &&  “ (PrefixMinimum text (k + 1 ) mn ) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn < (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (SpecPrefix text (k + 1 ) (app (out_2) ((cons (1) ((@nil Z))))) )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) >= mn)) (PreH2 : (mn < (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out_2 )) ,
  (PrefixMinimum text (k + 1 ) mn )
.

Definition solver_return_wit_1 := 
(
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (PrefixMinimum text k mn )) (PreH9 : (SpecPrefix text k out_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre k out_2 )
  **  (CharArray.undef_seg win_pre k n_pre )
|--
  EX (out: (@list Z)) ,
  “ (Spec text out ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre n_pre out )
) \/
(
forall (win_pre: Z) (n_pre: Z) (text: (@list Z)) (out_2: (@list Z)) (mn: Z) (k: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (PrefixMinimum text k mn )) (PreH9 : (SpecPrefix text k out_2 )) ,
  (CharArray.full win_pre k out_2 )
|--
  EX (out: (@list Z)) ,
  “ (Spec text out ) ”
  &&  (CharArray.full win_pre n_pre out )
).

Definition solver_partial_solve_wit_1 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : (0 <= k)) (PreH7 : (k <= n_pre)) (PreH8 : (PrefixMinimum text k mn )) (PreH9 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre k out )
  **  (CharArray.undef_seg win_pre k n_pre )
|--
  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (PrefixMinimum text k mn ) ” 
  &&  “ (SpecPrefix text k out ) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char  |-> (Znth k text 0))
  **  (CharArray.missing_i s_pre k 0 n_pre text )
  **  (CharArray.full win_pre k out )
  **  (CharArray.undef_seg win_pre k n_pre )
.

Definition solver_partial_solve_wit_2 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : (mn >= (Znth k text 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn )) (PreH10 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre k out )
  **  (CharArray.undef_seg win_pre k n_pre )
|--
  “ (mn >= (Znth k text 0)) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (PrefixMinimum text k mn ) ” 
  &&  “ (SpecPrefix text k out ) ”
  &&  (((win_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre k out )
.

Definition solver_partial_solve_wit_3 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : (mn < (Znth k text 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn )) (PreH10 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre k out )
  **  (CharArray.undef_seg win_pre k n_pre )
|--
  “ (mn < (Znth k text 0)) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (PrefixMinimum text k mn ) ” 
  &&  “ (SpecPrefix text k out ) ”
  &&  (((win_pre + (k * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre k out )
.

Definition solver_partial_solve_wit_4 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : (mn >= (Znth k text 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn )) (PreH10 : (SpecPrefix text k out )) ,
  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  (CharArray.full s_pre n_pre text )
|--
  “ (mn >= (Znth k text 0)) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (PrefixMinimum text k mn ) ” 
  &&  “ (SpecPrefix text k out ) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char  |-> (Znth k text 0))
  **  (CharArray.missing_i s_pre k 0 n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
.

Definition solver_partial_solve_wit_5 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : (mn < (Znth k text 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (0 <= k)) (PreH8 : (k <= n_pre)) (PreH9 : (PrefixMinimum text k mn )) (PreH10 : (SpecPrefix text k out )) ,
  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (1) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
  **  (CharArray.full s_pre n_pre text )
|--
  “ (mn < (Znth k text 0)) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (PrefixMinimum text k mn ) ” 
  &&  “ (SpecPrefix text k out ) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char  |-> (Znth k text 0))
  **  (CharArray.missing_i s_pre k 0 n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (1) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
.

Definition solver_partial_solve_wit_6 := 
forall (win_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (out: (@list Z)) (mn: Z) (k: Z) (PreH1 : ((Znth k text 0) < mn)) (PreH2 : (mn >= (Znth k text 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (0 <= k)) (PreH9 : (k <= n_pre)) (PreH10 : (PrefixMinimum text k mn )) (PreH11 : (SpecPrefix text k out )) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
|--
  “ ((Znth k text 0) < mn) ” 
  &&  “ (mn >= (Znth k text 0)) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((97 <= (Znth i text 0)) /\ ((Znth i text 0) <= 122))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (PrefixMinimum text k mn ) ” 
  &&  “ (SpecPrefix text k out ) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char  |-> (Znth k text 0))
  **  (CharArray.missing_i s_pre k 0 n_pre text )
  **  (CharArray.full win_pre (k + 1 ) (app (out) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg win_pre (k + 1 ) n_pre )
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

End VC_Correct.
