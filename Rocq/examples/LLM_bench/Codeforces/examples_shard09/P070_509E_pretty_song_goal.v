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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P070_509E_pretty_song_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (old_pre0: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (old_pre0: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (pre_values)) = (i + 1 ))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH9 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition solver_safety_wit_5 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition solver_safety_wit_6 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition solver_safety_wit_7 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (79 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 79) ”
.

Definition solver_safety_wit_8 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (85 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 85) ”
.

Definition solver_safety_wit_9 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |->_)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (89 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 89) ”
.

Definition solver_safety_wit_10 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 0)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_20 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 1)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_23 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "v" ) )) # Int  |-> 0)
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
).

Definition solver_safety_wit_24_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
.

Definition solver_safety_wit_25 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
).

Definition solver_safety_wit_25_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_25_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
.

Definition solver_safety_wit_26 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
).

Definition solver_safety_wit_26_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
.

Definition solver_safety_wit_27 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
).

Definition solver_safety_wit_27_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_27_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
.

Definition solver_safety_wit_28 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
).

Definition solver_safety_wit_28_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_28_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
.

Definition solver_safety_wit_29 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
).

Definition solver_safety_wit_29_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_29_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 1)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ”
.

Definition solver_safety_wit_30 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 0 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 0 )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 0 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 0 )) ”
).

Definition solver_safety_wit_30_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 0 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_30_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "v" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "c" ) )) # Char  |-> (Znth i text 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 0 )) ”
.

Definition solver_safety_wit_31 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_33 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_34 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_35 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_37 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0) + 0 )) ((app (pre_values) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_38 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_pp0: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH7 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 pre_values 0))
  **  (Int64Array.missing_i pre_pre 0 0 (n_pre + 1 ) pre_values )
  **  (((pp_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pp0)
  **  (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_39 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_pp0: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH7 : (VowelPrefixCounts text pre_values )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 pre_values 0))
  **  (Int64Array.missing_i pre_pre 0 0 (n_pre + 1 ) pre_values )
  **  (((pp_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pp0)
  **  (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_40 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH7 : ((Zlength (pp_values)) = 1)) (PreH8 : ((Znth 0 pp_values 0) = (Znth 0 pre_values 0))) (PreH9 : (VowelPrefixCounts text pre_values )) (PreH10 : (PrefixCountTotals pre_values pp_values )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 1 pp_values )
  **  (Int64Array.seg_shape pp_pre 1 (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_41 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (Int64Array.full pp_pre (i + 1 ) (replace_Znth (i) (((Znth ((i - 1 ) - 0 ) pp_values 0) + (Znth i pre_values 0) )) ((app (pp_values) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_42 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ (((Znth ((i - 1 ) - 0 ) pp_values 0) + (Znth i pre_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) pp_values 0) + (Znth i pre_values 0) )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ (((Znth ((i - 1 ) - 0 ) pp_values 0) + (Znth i pre_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) pp_values 0) + (Znth i pre_values 0) )) ”
).

Definition solver_safety_wit_42_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ (((Znth ((i - 1 ) - 0 ) pp_values 0) + (Znth i pre_values 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_42_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) pp_values 0) + (Znth i pre_values 0) )) ”
.

Definition solver_safety_wit_43 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 i pp_values )
  **  (((pp_pre + (i * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_44 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 i pp_values )
  **  (((pp_pre + (i * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_45 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH6 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH9 : (VowelPrefixCounts text pre_values )) (PreH10 : (PrefixCountTotals pre_values pp_values )) ,
  ((( &( "L" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_46 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) )) ”
).

Definition solver_safety_wit_46_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_46_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((INT64_MIN) <= ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) )) ”
.

Definition solver_safety_wit_47 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((L - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (L - 1 )) ”
.

Definition solver_safety_wit_48 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "hi" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_49 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  ((( &( "lo" ) )) # Int64  |->_)
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((n_pre - L ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - L )) ”
.

Definition solver_safety_wit_50 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "lo" ) )) # Int64  |-> (Znth (n_pre - L ) pp_values 0))
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((L - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (L - 1 )) ”
.

Definition solver_safety_wit_51 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "lo" ) )) # Int64  |-> (Znth (n_pre - L ) pp_values 0))
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_52 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "lo" ) )) # Int64  |-> (Znth (n_pre - L ) pp_values 0))
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) - (Znth (n_pre - L ) pp_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) - (Znth (n_pre - L ) pp_values 0) )) ”
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "lo" ) )) # Int64  |-> (Znth (n_pre - L ) pp_values 0))
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) - (Znth (n_pre - L ) pp_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) - (Znth (n_pre - L ) pp_values 0) )) ”
).

Definition solver_safety_wit_52_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "lo" ) )) # Int64  |-> (Znth (n_pre - L ) pp_values 0))
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) - (Znth (n_pre - L ) pp_values 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_52_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "lo" ) )) # Int64  |-> (Znth (n_pre - L ) pp_values 0))
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  ((( &( "hi" ) )) # Int64  |-> ((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((INT64_MIN) <= (((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) - (Znth (n_pre - L ) pp_values 0) )) ”
.

Definition solver_safety_wit_53 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full term_pre ((L - 1 ) + 1 ) (replace_Znth ((L - 1 )) ((((Znth n_pre pp_values 0) - (Znth (L - 1 ) pp_values 0) ) - (Znth (n_pre - L ) pp_values 0) )) ((app (terms) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "term" ) )) # Ptr  |-> term_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "pp" ) )) # Ptr  |-> pp_pre)
  **  ((( &( "L" ) )) # Int  |-> L)
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ ((L + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (L + 1 )) ”
.

Definition solver_entail_wit_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((65 <= (Znth i text 0)) /\ ((Znth i text 0) <= 90)))) (PreH4 : (n_pre = (Zlength (text)))) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (old_pre0: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pre0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_entail_wit_2 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (0 + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (0 + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 (0 + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (0 + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (PreH1 : (0 <= INT64_MAX)) (PreH2 : (0 >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) ,
  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> 0)
  **  (Int64Array.missing_i_shape pre_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (0 + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (0 + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 (0 + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre (0 + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_3 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values_2 )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (old_next: Z)  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ”
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ”
.

Definition solver_entail_wit_3_split_goal_spatial := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_entail_wit_4_1 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_4_2 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH11 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_4_3 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_4_4 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH11 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH11 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_4_5 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH13 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH13 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_4_6 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH15 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH15 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 1 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_4_7 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH15 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 0 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH15 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full pre_pre ((i + 1 ) + 1 ) (replace_Znth ((i + 1 )) (((Znth (i - 0 ) (app (pre_values_2) ((cons (old_next) ((@nil Z))))) 0) + 0 )) ((app (pre_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = ((i + 1 ) + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < ((i + 1 ) + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) pre_values )
  **  (Int64Array.seg_shape pre_pre ((i + 1 ) + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_entail_wit_5 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values_2 )
  **  (Int64Array.seg_shape pre_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  EX (old_pp0: Z)  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 pre_values 0))
  **  (Int64Array.missing_i pre_pre 0 0 (n_pre + 1 ) pre_values )
  **  (((pp_pre + (0 * sizeof(INT64)))) # Int64  |-> old_pp0)
  **  (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (pre_values_2)) = (i + 1 ))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (i + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH10 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1 ) )
  **  (Int64Array.missing_i pre_pre 0 0 (i + 1 ) pre_values_2 )
  **  (Int64Array.full_shape term_pre n_pre )
|--
  EX (pre_values: (@list Z)) ,
  “ ((Znth 0 pre_values 0) = (Znth (0 - 0 ) pre_values_2 0)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i pre_pre 0 0 (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1 ) )
).

Definition solver_entail_wit_6 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH7 : (VowelPrefixCounts text pre_values_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 pre_values_2 0))
  **  (Int64Array.missing_i pre_pre 0 0 (n_pre + 1 ) pre_values_2 )
  **  (((pp_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 pre_values_2 0))
  **  (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1 ) )
|--
  EX (pp_values: (@list Z))  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ ((Zlength (pp_values)) = 1) ” 
  &&  “ ((Znth 0 pp_values 0) = (Znth 0 pre_values 0)) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 1 pp_values )
  **  (Int64Array.seg_shape pp_pre 1 (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (PreH1 : ((Znth 0 pre_values_2 0) <= INT64_MAX)) (PreH2 : ((Znth 0 pre_values_2 0) >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((65 <= (Znth k_3 text 0)) /\ ((Znth k_3 text 0) <= 90)))) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (n_pre + 1 ))) -> ((0 <= (Znth k_4 pre_values_2 0)) /\ ((Znth k_4 pre_values_2 0) <= k_4)))) (PreH9 : (VowelPrefixCounts text pre_values_2 )) ,
  (Int64Array.full_shape term_pre n_pre )
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 pre_values_2 0))
  **  (Int64Array.missing_i pre_pre 0 0 (n_pre + 1 ) pre_values_2 )
  **  (((pp_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 pre_values_2 0))
  **  (Int64Array.missing_i_shape pp_pre 0 0 (n_pre + 1 ) )
|--
  EX (pp_values: (@list Z))  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ ((Zlength (pp_values)) = 1) ” 
  &&  “ ((Znth 0 pp_values 0) = (Znth 0 pre_values 0)) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 1 pp_values )
  **  (Int64Array.seg_shape pp_pre 1 (n_pre + 1 ) )
).

Definition solver_entail_wit_7 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH7 : ((Zlength (pp_values_2)) = 1)) (PreH8 : ((Znth 0 pp_values_2 0) = (Znth 0 pre_values_2 0))) (PreH9 : (VowelPrefixCounts text pre_values_2 )) (PreH10 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg pp_pre 0 1 pp_values_2 )
  **  (Int64Array.seg_shape pp_pre 1 (n_pre + 1 ) )
|--
  EX (pp_values: (@list Z))  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = 1) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 1)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 1 pp_values )
  **  (Int64Array.seg_shape pp_pre 1 (n_pre + 1 ) )
) \/
(
forall (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH7 : ((Zlength (pp_values_2)) = 1)) (PreH8 : ((Znth 0 pp_values_2 0) = (Znth 0 pre_values_2 0))) (PreH9 : (VowelPrefixCounts text pre_values_2 )) (PreH10 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  TT && emp 
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 1)) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH6 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH7 : ((Zlength (pp_values_2)) = 1)) (PreH8 : ((Znth 0 pp_values_2 0) = (Znth 0 pre_values_2 0))) (PreH9 : (VowelPrefixCounts text pre_values_2 )) (PreH10 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 1)) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))
.

Definition solver_entail_wit_8 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg pp_pre 0 i pp_values_2 )
  **  (Int64Array.seg_shape pp_pre i (n_pre + 1 ) )
|--
  EX (old_next: Z)  (pp_values: (@list Z))  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 i pp_values )
  **  (((pp_pre + (i * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.seg_shape pp_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (pp_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.seg_shape pp_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ”
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (pp_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.seg_shape pp_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ”
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (pp_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.seg_shape pp_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ”
.

Definition solver_entail_wit_8_split_goal_spatial := 
forall (pp_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.seg_shape pp_pre (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape term_pre n_pre )
|--
  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
.

Definition solver_entail_wit_9 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values_2)) = i)) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values_2 )) (PreH12 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.full pp_pre (i + 1 ) (replace_Znth (i) (((Znth ((i - 1 ) - 0 ) pp_values_2 0) + (Znth i pre_values_2 0) )) ((app (pp_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  EX (pp_values: (@list Z))  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) pp_values )
  **  (Int64Array.seg_shape pp_pre (i + 1 ) (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values_2)) = i)) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values_2 )) (PreH12 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.full pp_pre (i + 1 ) (replace_Znth (i) (((Znth ((i - 1 ) - 0 ) pp_values_2 0) + (Znth i pre_values_2 0) )) ((app (pp_values_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  EX (pp_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values_2 ) ” 
  &&  “ (PrefixCountTotals pre_values_2 pp_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) pp_values )
  **  (Int64Array.seg_shape pp_pre (i + 1 ) (n_pre + 1 ) )
).

Definition solver_entail_wit_10 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.seg pp_pre 0 i pp_values_2 )
  **  (Int64Array.seg_shape pp_pre i (n_pre + 1 ) )
|--
  EX (pp_values: (@list Z))  (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
) \/
(
forall (pp_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((65 <= (Znth k_4 text 0)) /\ ((Znth k_4 text 0) <= 90)))) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = i)) (PreH10 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (n_pre + 1 ))) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= k_5)))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < i)) -> ((0 <= (Znth k_6 pp_values_2 0)) /\ ((Znth k_6 pp_values_2 0) <= ((k_6 * (k_6 + 1 ) ) ÷ 2 ))))) (PreH12 : (VowelPrefixCounts text pre_values_2 )) (PreH13 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pp_pre 0 i pp_values_2 )
|--
  EX (pp_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values_2 ) ” 
  &&  “ (PrefixCountTotals pre_values_2 pp_values ) ”
  &&  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
).

Definition solver_entail_wit_11 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH6 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH8 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH9 : (VowelPrefixCounts text pre_values_2 )) (PreH10 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values_2 )
|--
  EX (pp_values: (@list Z))  (pre_values: (@list Z))  (terms: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (terms)) = (1 - 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (1 - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 (1 - 1 ) terms )
  **  (Int64Array.seg_shape term_pre (1 - 1 ) n_pre )
) \/
(
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH5 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH6 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH7 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH8 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH9 : (VowelPrefixCounts text pre_values_2 )) (PreH10 : (PrefixCountTotals pre_values_2 pp_values_2 )) ,
  (Int64Array.full_shape term_pre n_pre )
|--
  EX (terms: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (terms)) = (1 - 1 )) ” 
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values_2)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (1 - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values_2 ) ” 
  &&  “ (PrefixCountTotals pre_values_2 pp_values_2 ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (Int64Array.seg term_pre 0 (1 - 1 ) terms )
  **  (Int64Array.seg_shape term_pre (1 - 1 ) n_pre )
).

Definition solver_entail_wit_12 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) (PreH15 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values_2 )
  **  (Int64Array.seg term_pre 0 (L - 1 ) terms_2 )
  **  (Int64Array.seg_shape term_pre (L - 1 ) n_pre )
|--
  EX (old_next: Z)  (pp_values: (@list Z))  (pre_values: (@list Z))  (terms: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= L) ” 
  &&  “ (L <= n_pre) ” 
  &&  “ ((Zlength (terms)) = (L - 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 (L - 1 ) terms )
  **  (((term_pre + ((L - 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
) \/
(
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) (PreH15 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.seg_shape term_pre ((L - 1 ) + 1 ) n_pre )
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms_2 0)) /\ ((Znth k_4 terms_2 0) <= (n_pre * n_pre )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ”
  &&  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
).

Definition solver_entail_wit_12_split_goal_1 := 
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) (PreH15 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.seg_shape term_pre ((L - 1 ) + 1 ) n_pre )
|--
  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms_2 0)) /\ ((Znth k_4 terms_2 0) <= (n_pre * n_pre )))) ”
.

Definition solver_entail_wit_12_split_goal_2 := 
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) (PreH15 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.seg_shape term_pre ((L - 1 ) + 1 ) n_pre )
|--
  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ”
.

Definition solver_entail_wit_12_split_goal_3 := 
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) (PreH15 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.seg_shape term_pre ((L - 1 ) + 1 ) n_pre )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ”
.

Definition solver_entail_wit_12_split_goal_4 := 
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) (PreH15 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.seg_shape term_pre ((L - 1 ) + 1 ) n_pre )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ”
.

Definition solver_entail_wit_12_split_goal_spatial := 
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values_2: (@list Z)) (pre_values_2: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH11 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH12 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values_2 )) (PreH15 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.seg_shape term_pre ((L - 1 ) + 1 ) n_pre )
|--
  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
.

Definition solver_entail_wit_13 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (terms_2: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms_2)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH11 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values_2 )) (PreH14 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH15 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.full term_pre ((L - 1 ) + 1 ) (replace_Znth ((L - 1 )) ((((Znth n_pre pp_values_2 0) - (Znth (L - 1 ) pp_values_2 0) ) - (Znth (n_pre - L ) pp_values_2 0) )) ((app (terms_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values_2 )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values_2 )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  EX (pp_values: (@list Z))  (pre_values: (@list Z))  (terms: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= (L + 1 )) ” 
  &&  “ ((L + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (terms)) = ((L + 1 ) - 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < ((L + 1 ) - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L + 1 ) - 1 ) terms )
  **  (Int64Array.seg_shape term_pre ((L + 1 ) - 1 ) n_pre )
) \/
(
forall (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pre_values_2: (@list Z)) (pp_values_2: (@list Z)) (terms_2: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((65 <= (Znth k_5 text 0)) /\ ((Znth k_5 text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms_2)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values_2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values_2)) = (n_pre + 1 ))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (n_pre + 1 ))) -> ((0 <= (Znth k_6 pre_values_2 0)) /\ ((Znth k_6 pre_values_2 0) <= k_6)))) (PreH11 : forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < (n_pre + 1 ))) -> ((0 <= (Znth k_7 pp_values_2 0)) /\ ((Znth k_7 pp_values_2 0) <= ((k_7 * (k_7 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_8: Z) , (((0 <= k_8) /\ (k_8 < (L - 1 ))) -> ((0 <= (Znth k_8 terms_2 0)) /\ ((Znth k_8 terms_2 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values_2 )) (PreH14 : (PrefixCountTotals pre_values_2 pp_values_2 )) (PreH15 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.full term_pre ((L - 1 ) + 1 ) (replace_Znth ((L - 1 )) ((((Znth n_pre pp_values_2 0) - (Znth (L - 1 ) pp_values_2 0) ) - (Znth (n_pre - L ) pp_values_2 0) )) ((app (terms_2) ((cons (old_next) ((@nil Z))))))) )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  EX (terms: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= (L + 1 )) ” 
  &&  “ ((L + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (terms)) = ((L + 1 ) - 1 )) ” 
  &&  “ ((Zlength (pre_values_2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values_2)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values_2 0)) /\ ((Znth k_2 pre_values_2 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values_2 0)) /\ ((Znth k_3 pp_values_2 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < ((L + 1 ) - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values_2 ) ” 
  &&  “ (PrefixCountTotals pre_values_2 pp_values_2 ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (Int64Array.seg term_pre 0 ((L + 1 ) - 1 ) terms )
  **  (Int64Array.seg_shape term_pre ((L + 1 ) - 1 ) n_pre )
).

Definition solver_return_wit_1 := 
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pp_values: (@list Z)) (pre_values: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms_2 0)) /\ ((Znth k_4 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values )) (PreH15 : (PrefixCountTotals pre_values pp_values )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 (L - 1 ) terms_2 )
  **  (Int64Array.seg_shape term_pre (L - 1 ) n_pre )
|--
  EX (terms: (@list Z))  (real_out: R) ,
  “ (Spec text real_out ) ” 
  &&  “ (PrettyTerms text terms real_out ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full term_pre n_pre terms )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
) \/
(
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (text: (@list Z)) (pp_values: (@list Z)) (pre_values: (@list Z)) (terms_2: (@list Z)) (L: Z) (PreH1 : (L > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (1 <= L)) (PreH7 : (L <= (n_pre + 1 ))) (PreH8 : ((Zlength (terms_2)) = (L - 1 ))) (PreH9 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH10 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms_2 0)) /\ ((Znth k_4 terms_2 0) <= (n_pre * n_pre ))))) (PreH14 : (VowelPrefixCounts text pre_values )) (PreH15 : (PrefixCountTotals pre_values pp_values )) (PreH16 : (PrettyTermPrefix text terms_2 )) ,
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 (L - 1 ) terms_2 )
|--
  EX (terms: (@list Z))  (real_out: R) ,
  “ (Spec text real_out ) ” 
  &&  “ (PrettyTerms text terms real_out ) ”
  &&  (Int64Array.full term_pre n_pre terms )
  **  (Int64Array.full_shape pre_pre (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
).

Definition solver_partial_solve_wit_1 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (pre_values)) = (i + 1 ))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH9 : (VowelPrefixCounts text pre_values )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i text 0))
  **  (CharArray.missing_i s_pre i 0 n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_2 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 85) ” 
  &&  “ ((Znth i text 0) <> 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_3 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 85)) (PreH2 : ((Znth i text 0) <> 79)) (PreH3 : ((Znth i text 0) <> 73)) (PreH4 : ((Znth i text 0) <> 69)) (PreH5 : ((Znth i text 0) <> 65)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 500000)) (PreH8 : (n_pre = (Zlength (text)))) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((Zlength (pre_values)) = (i + 1 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH14 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 85) ” 
  &&  “ ((Znth i text 0) <> 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_4 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_5 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 73)) (PreH2 : ((Znth i text 0) <> 69)) (PreH3 : ((Znth i text 0) <> 65)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 500000)) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (pre_values)) = (i + 1 ))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH12 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_6 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_7 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 65)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 500000)) (PreH4 : (n_pre = (Zlength (text)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (pre_values)) = (i + 1 ))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_8 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_9 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 69)) (PreH2 : ((Znth i text 0) <> 65)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 500000)) (PreH5 : (n_pre = (Zlength (text)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (pre_values)) = (i + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_10 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_11 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 79)) (PreH2 : ((Znth i text 0) <> 73)) (PreH3 : ((Znth i text 0) <> 69)) (PreH4 : ((Znth i text 0) <> 65)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 500000)) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((Zlength (pre_values)) = (i + 1 ))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH13 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_12 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 89) ” 
  &&  “ ((Znth i text 0) <> 85) ” 
  &&  “ ((Znth i text 0) <> 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_13 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) = 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) = 89) ” 
  &&  “ ((Znth i text 0) <> 85) ” 
  &&  “ ((Znth i text 0) <> 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_14 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) <> 89) ” 
  &&  “ ((Znth i text 0) <> 85) ” 
  &&  “ ((Znth i text 0) <> 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth (i - 0 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) 0))
  **  (Int64Array.missing_i pre_pre i 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_15 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : ((Znth i text 0) <> 89)) (PreH2 : ((Znth i text 0) <> 85)) (PreH3 : ((Znth i text 0) <> 79)) (PreH4 : ((Znth i text 0) <> 73)) (PreH5 : ((Znth i text 0) <> 69)) (PreH6 : ((Znth i text 0) <> 65)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 500000)) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (pre_values)) = (i + 1 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH15 : (VowelPrefixCounts text pre_values )) ,
  (Int64Array.seg pre_pre 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
|--
  “ ((Znth i text 0) <> 89) ” 
  &&  “ ((Znth i text 0) <> 85) ” 
  &&  “ ((Znth i text 0) <> 79) ” 
  &&  “ ((Znth i text 0) <> 73) ” 
  &&  “ ((Znth i text 0) <> 69) ” 
  &&  “ ((Znth i text 0) <> 65) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ”
  &&  (((pre_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pre_pre (i + 1 ) 0 ((i + 1 ) + 1 ) (app (pre_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pre_pre (i + 1 ) (i + 1 ) (n_pre + 1 ) )
  **  (Int64Array.full_shape pp_pre (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_16 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 i pp_values )
  **  (((pp_pre + (i * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (((pp_pre + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - 1 ) - 0 ) pp_values 0))
  **  (Int64Array.missing_i pp_pre (i - 1 ) 0 i pp_values )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (((pp_pre + (i * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_17 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (Int64Array.seg pp_pre 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i pre_values 0))
  **  (Int64Array.missing_i pre_pre i 0 (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_18 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (old_next: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH8 : ((Zlength (pp_values)) = i)) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH11 : (VowelPrefixCounts text pre_values )) (PreH12 : (PrefixCountTotals pre_values pp_values )) ,
  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg pp_pre 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ”
  &&  (((pp_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i pp_pre i 0 (i + 1 ) (app (pp_values) ((cons (old_next) ((@nil Z))))) )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full_shape term_pre n_pre )
  **  (Int64Array.missing_i_shape pp_pre i i (n_pre + 1 ) )
.

Definition solver_partial_solve_wit_19 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 (L - 1 ) terms )
  **  (((term_pre + ((L - 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= L) ” 
  &&  “ (L <= n_pre) ” 
  &&  “ ((Zlength (terms)) = (L - 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (((pp_pre + (n_pre * sizeof(INT64)))) # Int64  |-> (Znth n_pre pp_values 0))
  **  (Int64Array.missing_i pp_pre n_pre 0 (n_pre + 1 ) pp_values )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.seg term_pre 0 (L - 1 ) terms )
  **  (((term_pre + ((L - 1 ) * sizeof(INT64)))) # Int64  |-> old_next)
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
.

Definition solver_partial_solve_wit_20 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= L) ” 
  &&  “ (L <= n_pre) ” 
  &&  “ ((Zlength (terms)) = (L - 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (((pp_pre + ((L - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (L - 1 ) pp_values 0))
  **  (Int64Array.missing_i pp_pre (L - 1 ) 0 (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
.

Definition solver_partial_solve_wit_21 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= L) ” 
  &&  “ (L <= n_pre) ” 
  &&  “ ((Zlength (terms)) = (L - 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (((pp_pre + ((n_pre - L ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - L ) pp_values 0))
  **  (Int64Array.missing_i pp_pre (n_pre - L ) 0 (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
.

Definition solver_partial_solve_wit_22 := 
forall (pp_pre: Z) (pre_pre: Z) (term_pre: Z) (n_pre: Z) (s_pre: Z) (text: (@list Z)) (pre_values: (@list Z)) (pp_values: (@list Z)) (terms: (@list Z)) (old_next: Z) (L: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 500000)) (PreH3 : (n_pre = (Zlength (text)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90)))) (PreH5 : (1 <= L)) (PreH6 : (L <= n_pre)) (PreH7 : ((Zlength (terms)) = (L - 1 ))) (PreH8 : ((Zlength (pre_values)) = (n_pre + 1 ))) (PreH9 : ((Zlength (pp_values)) = (n_pre + 1 ))) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2)))) (PreH11 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 ))))) (PreH12 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre ))))) (PreH13 : (VowelPrefixCounts text pre_values )) (PreH14 : (PrefixCountTotals pre_values pp_values )) (PreH15 : (PrettyTermPrefix text terms )) ,
  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (Int64Array.seg term_pre 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 500000) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((65 <= (Znth k text 0)) /\ ((Znth k text 0) <= 90))) ” 
  &&  “ (1 <= L) ” 
  &&  “ (L <= n_pre) ” 
  &&  “ ((Zlength (terms)) = (L - 1 )) ” 
  &&  “ ((Zlength (pre_values)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (pp_values)) = (n_pre + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((0 <= (Znth k_2 pre_values 0)) /\ ((Znth k_2 pre_values 0) <= k_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (n_pre + 1 ))) -> ((0 <= (Znth k_3 pp_values 0)) /\ ((Znth k_3 pp_values 0) <= ((k_3 * (k_3 + 1 ) ) ÷ 2 )))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (L - 1 ))) -> ((0 <= (Znth k_4 terms 0)) /\ ((Znth k_4 terms 0) <= (n_pre * n_pre )))) ” 
  &&  “ (VowelPrefixCounts text pre_values ) ” 
  &&  “ (PrefixCountTotals pre_values pp_values ) ” 
  &&  “ (PrettyTermPrefix text terms ) ”
  &&  (((term_pre + ((L - 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i term_pre (L - 1 ) 0 ((L - 1 ) + 1 ) (app (terms) ((cons (old_next) ((@nil Z))))) )
  **  (Int64Array.full pp_pre (n_pre + 1 ) pp_values )
  **  (CharArray.full s_pre n_pre text )
  **  (Int64Array.full pre_pre (n_pre + 1 ) pre_values )
  **  (Int64Array.missing_i_shape term_pre (L - 1 ) (L - 1 ) n_pre )
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
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Axiom proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5.
Axiom proof_of_solver_entail_wit_4_6 : solver_entail_wit_4_6.
Axiom proof_of_solver_entail_wit_4_7 : solver_entail_wit_4_7.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
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

End VC_Correct.
