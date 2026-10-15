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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P051_639B_bear_and_forgotten_tree_3_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ ((2 * h_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * h_pre )) ”
.

Definition solver_safety_wit_2 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre < h_pre)) (PreH2 : (d_pre <= (2 * h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_4 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre >= h_pre)) (PreH2 : (d_pre <= (2 * h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre = 1)) (PreH2 : (d_pre >= h_pre)) (PreH3 : (d_pre <= (2 * h_pre ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= h_pre)) (PreH7 : (h_pre <= d_pre)) (PreH8 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (n_pre > 2)) (PreH2 : (d_pre = 1)) (PreH3 : (d_pre >= h_pre)) (PreH4 : (d_pre <= (2 * h_pre ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= h_pre)) (PreH8 : (h_pre <= d_pre)) (PreH9 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_7 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre > (2 * h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_8 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre > (2 * h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (n_pre > 2)) (PreH2 : (d_pre = 1)) (PreH3 : (d_pre >= h_pre)) (PreH4 : (d_pre <= (2 * h_pre ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= h_pre)) (PreH8 : (h_pre <= d_pre)) (PreH9 : (d_pre <= (n_pre - 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_12 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  ((( &( "last" ) )) # Int  |->_)
  **  ((( &( "next" ) )) # Int  |-> 2)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "last" ) )) # Int  |-> 1)
  **  ((( &( "next" ) )) # Int  |-> 2)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> next)
|--
  “ ((next + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (next + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> (next + 1 ))
  **  ((( &( "last" ) )) # Int  |-> next)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i >= h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i >= h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> 1)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) (PreH7 : (0 <= i)) (PreH8 : (i <= (d_pre - h_pre ))) (PreH9 : (count = (h_pre + i ))) (PreH10 : (next = ((h_pre + i ) + 2 ))) (PreH11 : (i = 0)) (PreH12 : (last = 1)) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ ((d_pre - h_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d_pre - h_pre )) ”
.

Definition solver_safety_wit_20 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) (PreH7 : (0 <= i)) (PreH8 : (i <= (d_pre - h_pre ))) (PreH9 : (count = (h_pre + i ))) (PreH10 : (next = ((h_pre + i ) + 2 ))) (PreH11 : (0 < i)) (PreH12 : (last = ((h_pre + i ) + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ ((d_pre - h_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d_pre - h_pre )) ”
.

Definition solver_safety_wit_21 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_22 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> next)
|--
  “ ((next + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (next + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> next)
|--
  “ ((next + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (next + 1 )) ”
.

Definition solver_safety_wit_25 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> (next + 1 ))
  **  ((( &( "last" ) )) # Int  |-> next)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> (next + 1 ))
  **  ((( &( "last" ) )) # Int  |-> next)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_27 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre = h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (0 < i)) (PreH14 : (last = ((h_pre + i ) + 1 ))) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "attach" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_28 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre <> h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (0 < i)) (PreH14 : (last = ((h_pre + i ) + 1 ))) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "attach" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_29 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre <> h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (i = 0)) (PreH14 : (last = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "attach" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_30 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre = h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (i = 0)) (PreH14 : (last = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "attach" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_31 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_32 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_33 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_34 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ False ”
.

Definition solver_safety_wit_35 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition solver_safety_wit_37 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
|--
  “ ((next + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (next + 1 )) ”
.

Definition solver_safety_wit_38 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "h" ) )) # Int  |-> h_pre)
  **  ((( &( "eu" ) )) # Ptr  |-> eu_pre)
  **  ((( &( "ev" ) )) # Ptr  |-> ev_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "next" ) )) # Int  |-> next)
  **  ((( &( "last" ) )) # Int  |-> last)
  **  ((( &( "attach" ) )) # Int  |-> attach)
|--
  “ ((next + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (next + 1 )) ”
.

Definition solver_entail_wit_1_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= 2)) (PreH2 : (d_pre = 1)) (PreH3 : (d_pre >= h_pre)) (PreH4 : (d_pre <= (2 * h_pre ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= h_pre)) (PreH8 : (h_pre <= d_pre)) (PreH9 : (d_pre <= (n_pre - 1 ))) ,
  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ”
  &&  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= 2)) (PreH2 : (d_pre = 1)) (PreH3 : (d_pre >= h_pre)) (PreH4 : (d_pre <= (2 * h_pre ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= h_pre)) (PreH8 : (h_pre <= d_pre)) (PreH9 : (d_pre <= (n_pre - 1 ))) ,
  TT && emp 
|--
  “ (Feasible n_pre 1 h_pre ) ”
  &&  emp
).

Definition solver_entail_wit_1_1_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (n_pre <= 2)) (PreH2 : (d_pre = 1)) (PreH3 : (d_pre >= h_pre)) (PreH4 : (d_pre <= (2 * h_pre ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= h_pre)) (PreH8 : (h_pre <= d_pre)) (PreH9 : (d_pre <= (n_pre - 1 ))) ,
  (Feasible n_pre 1 h_pre )
.

Definition solver_entail_wit_1_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre <> 1)) (PreH2 : (d_pre >= h_pre)) (PreH3 : (d_pre <= (2 * h_pre ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= h_pre)) (PreH7 : (h_pre <= d_pre)) (PreH8 : (d_pre <= (n_pre - 1 ))) ,
  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ”
  &&  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre <> 1)) (PreH2 : (d_pre >= h_pre)) (PreH3 : (d_pre <= (2 * h_pre ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= h_pre)) (PreH7 : (h_pre <= d_pre)) (PreH8 : (d_pre <= (n_pre - 1 ))) ,
  TT && emp 
|--
  “ (Feasible n_pre d_pre h_pre ) ”
  &&  emp
).

Definition solver_entail_wit_1_2_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (d_pre <> 1)) (PreH2 : (d_pre >= h_pre)) (PreH3 : (d_pre <= (2 * h_pre ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= h_pre)) (PreH7 : (h_pre <= d_pre)) (PreH8 : (d_pre <= (n_pre - 1 ))) ,
  (Feasible n_pre d_pre h_pre )
.

Definition solver_entail_wit_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= h_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (2 = (0 + 2 )) ” 
  &&  “ (1 = (0 + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = 0) ” 
  &&  “ ((Zlength (ev_data)) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 0 eu_data )
  **  (IntArray.undef_seg eu_pre 0 (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 0 ev_data )
  **  (IntArray.undef_seg ev_pre 0 (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> (CanonicalEndpoints d_pre h_pre k (Znth k (@nil Z) 0) (Znth k (@nil Z) 0) )) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  forall (k: Z) , (((0 <= k) /\ (k < 0)) -> (CanonicalEndpoints d_pre h_pre k (Znth k (@nil Z) 0) (Znth k (@nil Z) 0) ))
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= h_pre)) (PreH4 : (h_pre <= d_pre)) (PreH5 : (d_pre <= (n_pre - 1 ))) (PreH6 : (Feasible n_pre d_pre h_pre )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_3 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data_2)) = count)) (PreH14 : ((Zlength (ev_data_2)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data_2) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data_2) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= h_pre) ” 
  &&  “ ((count + 1 ) = (i + 1 )) ” 
  &&  “ ((next + 1 ) = ((i + 1 ) + 2 )) ” 
  &&  “ (next = ((i + 1 ) + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = (count + 1 )) ” 
  &&  “ ((Zlength (ev_data)) = (count + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (count + 1 ))) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 (count + 1 ) eu_data )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 (count + 1 ) ev_data )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data_2)) = count)) (PreH14 : ((Zlength (ev_data_2)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  TT && emp 
|--
  “ ((Zlength ((app (ev_data_2) ((cons ((i + 2 )) ((@nil Z))))))) = (count + 1 )) ” 
  &&  “ ((Zlength ((app (eu_data_2) ((cons ((i + 1 )) ((@nil Z))))))) = (count + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data_2)) = count)) (PreH14 : ((Zlength (ev_data_2)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (ev_data_2) ((cons ((i + 2 )) ((@nil Z))))))) = (count + 1 ))
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data_2)) = count)) (PreH14 : ((Zlength (ev_data_2)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (eu_data_2) ((cons ((i + 1 )) ((@nil Z))))))) = (count + 1 ))
.

Definition solver_entail_wit_4 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i >= h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data_2)) = count)) (PreH14 : ((Zlength (ev_data_2)) = count)) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data_2 )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data_2 )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (d_pre - h_pre )) ” 
  &&  “ (count = (h_pre + 0 )) ” 
  &&  “ (next = ((h_pre + 0 ) + 2 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i >= h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data_2)) = count)) (PreH14 : ((Zlength (ev_data_2)) = count)) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) )) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i >= h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data_2)) = count)) (PreH14 : ((Zlength (ev_data_2)) = count)) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))
.

Definition solver_entail_wit_5_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data_2) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data_2) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (d_pre - h_pre )) ” 
  &&  “ ((count + 1 ) = (h_pre + (i + 1 ) )) ” 
  &&  “ ((next + 1 ) = ((h_pre + (i + 1 ) ) + 2 )) ” 
  &&  “ (0 < (i + 1 )) ” 
  &&  “ (next = ((h_pre + (i + 1 ) ) + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = (count + 1 )) ” 
  &&  “ ((Zlength (ev_data)) = (count + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (count + 1 ))) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 (count + 1 ) eu_data )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 (count + 1 ) ev_data )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  TT && emp 
|--
  “ ((Zlength ((app (ev_data_2) ((cons (((h_pre + i ) + 2 )) ((@nil Z))))))) = ((h_pre + i ) + 1 )) ” 
  &&  “ ((Zlength ((app (eu_data_2) ((cons (((h_pre + i ) + 1 )) ((@nil Z))))))) = ((h_pre + i ) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (ev_data_2) ((cons (((h_pre + i ) + 2 )) ((@nil Z))))))) = ((h_pre + i ) + 1 ))
.

Definition solver_entail_wit_5_1_split_goal_2 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (eu_data_2) ((cons (((h_pre + i ) + 1 )) ((@nil Z))))))) = ((h_pre + i ) + 1 ))
.

Definition solver_entail_wit_5_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data_2) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data_2) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (d_pre - h_pre )) ” 
  &&  “ ((count + 1 ) = (h_pre + (i + 1 ) )) ” 
  &&  “ ((next + 1 ) = ((h_pre + (i + 1 ) ) + 2 )) ” 
  &&  “ (0 < (i + 1 )) ” 
  &&  “ (next = ((h_pre + (i + 1 ) ) + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = (count + 1 )) ” 
  &&  “ ((Zlength (ev_data)) = (count + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (count + 1 ))) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 (count + 1 ) eu_data )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 (count + 1 ) ev_data )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  TT && emp 
|--
  “ ((Zlength ((app (ev_data_2) ((cons (((h_pre + 0 ) + 2 )) ((@nil Z))))))) = ((h_pre + 0 ) + 1 )) ” 
  &&  “ ((Zlength ((app (eu_data_2) ((cons (1) ((@nil Z))))))) = ((h_pre + 0 ) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (ev_data_2) ((cons (((h_pre + 0 ) + 2 )) ((@nil Z))))))) = ((h_pre + 0 ) + 1 ))
.

Definition solver_entail_wit_5_2_split_goal_2 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data_2)) = count)) (PreH15 : ((Zlength (ev_data_2)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (eu_data_2) ((cons (1) ((@nil Z))))))) = ((h_pre + 0 ) + 1 ))
.

Definition solver_entail_wit_6_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre <> h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (0 < i)) (PreH14 : (last = ((h_pre + i ) + 1 ))) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data_2 )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data_2 )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= count) ” 
  &&  “ (count <= (n_pre - 1 )) ” 
  &&  “ (next = (count + 2 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (last = (d_pre + 1 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre <> h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (0 < i)) (PreH14 : (last = ((h_pre + i ) + 1 ))) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) )) ”
  &&  emp
).

Definition solver_entail_wit_6_1_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre <> h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (0 < i)) (PreH14 : (last = ((h_pre + i ) + 1 ))) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))
.

Definition solver_entail_wit_6_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre = h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (i = 0)) (PreH14 : (last = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data_2 )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data_2 )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= count) ” 
  &&  “ (count <= (n_pre - 1 )) ” 
  &&  “ (next = (count + 2 )) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (last = 1) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (2 = 2) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre = h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (i = 0)) (PreH14 : (last = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) )) ”
  &&  emp
).

Definition solver_entail_wit_6_2_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (d_pre = h_pre)) (PreH2 : (i >= (d_pre - h_pre ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= h_pre)) (PreH6 : (h_pre <= d_pre)) (PreH7 : (d_pre <= (n_pre - 1 ))) (PreH8 : (Feasible n_pre d_pre h_pre )) (PreH9 : (0 <= i)) (PreH10 : (i <= (d_pre - h_pre ))) (PreH11 : (count = (h_pre + i ))) (PreH12 : (next = ((h_pre + i ) + 2 ))) (PreH13 : (i = 0)) (PreH14 : (last = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < count)) -> (CanonicalEndpoints d_pre h_pre k_2 (Znth k_2 eu_data_2 0) (Znth k_2 ev_data_2 0) ))) ,
  forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))
.

Definition solver_entail_wit_7_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data_2) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data_2) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((next + 1 ) = ((count + 1 ) + 2 )) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (last = 1) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (attach = 2) ” 
  &&  “ ((Zlength (eu_data)) = (count + 1 )) ” 
  &&  “ ((Zlength (ev_data)) = (count + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (count + 1 ))) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 (count + 1 ) eu_data )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 (count + 1 ) ev_data )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  TT && emp 
|--
  “ ((Zlength ((app (ev_data_2) ((cons ((count + 2 )) ((@nil Z))))))) = (count + 1 )) ” 
  &&  “ ((Zlength ((app (eu_data_2) ((cons (2) ((@nil Z))))))) = (count + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_7_1_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (ev_data_2) ((cons ((count + 2 )) ((@nil Z))))))) = (count + 1 ))
.

Definition solver_entail_wit_7_1_split_goal_2 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (eu_data_2) ((cons (2) ((@nil Z))))))) = (count + 1 ))
.

Definition solver_entail_wit_7_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg ev_pre 0 (count + 1 ) (app (ev_data_2) ((cons (next) ((@nil Z))))) )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data_2) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((next + 1 ) = ((count + 1 ) + 2 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (last = (d_pre + 1 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (attach = 1) ” 
  &&  “ ((Zlength (eu_data)) = (count + 1 )) ” 
  &&  “ ((Zlength (ev_data)) = (count + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (count + 1 ))) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (IntArray.seg eu_pre 0 (count + 1 ) eu_data )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 (count + 1 ) ev_data )
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
) \/
(
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  TT && emp 
|--
  “ ((Zlength ((app (ev_data_2) ((cons ((count + 2 )) ((@nil Z))))))) = (count + 1 )) ” 
  &&  “ ((Zlength ((app (eu_data_2) ((cons (1) ((@nil Z))))))) = (count + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_7_2_split_goal_1 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (ev_data_2) ((cons ((count + 2 )) ((@nil Z))))))) = (count + 1 ))
.

Definition solver_entail_wit_7_2_split_goal_2 := 
forall (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  ((Zlength ((app (eu_data_2) ((cons (1) ((@nil Z))))))) = (count + 1 ))
.

Definition solver_return_wit_1 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z)  __default__Prod_Z_Z (PreH1 : (next > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data_2 )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data_2 )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z))  (edges: (@list (Z * Z))) ,
  “ (Spec n_pre d_pre h_pre (Some (edges)) ) ” 
  &&  “ (count = (Zlength (edges))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> (((Znth i eu_data 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i ev_data 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z)  __default__Prod_Z_Z (PreH1 : (next > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data_2 )
  **  (IntArray.seg ev_pre 0 count ev_data_2 )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z))  (edges: (@list (Z * Z))) ,
  “ (Spec n_pre d_pre h_pre (Some (edges)) ) ” 
  &&  “ (count = (Zlength (edges))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> (((Znth i eu_data 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i ev_data 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
).

Definition solver_return_wit_2 := 
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z)  __default__Prod_Z_Z (PreH1 : (next > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data_2 )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data_2 )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z))  (edges: (@list (Z * Z))) ,
  “ (Spec n_pre d_pre h_pre (Some (edges)) ) ” 
  &&  “ (count = (Zlength (edges))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> (((Znth i eu_data 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i ev_data 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
) \/
(
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data_2: (@list Z)) (eu_data_2: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z)  __default__Prod_Z_Z (PreH1 : (next > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data_2)) = count)) (PreH16 : ((Zlength (ev_data_2)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data_2 0) (Znth k ev_data_2 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data_2 )
  **  (IntArray.seg ev_pre 0 count ev_data_2 )
|--
  EX (ev_data: (@list Z))  (eu_data: (@list Z))  (edges: (@list (Z * Z))) ,
  “ (Spec n_pre d_pre h_pre (Some (edges)) ) ” 
  &&  “ (count = (Zlength (edges))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> (((Znth i eu_data 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i ev_data 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data )
).

Definition solver_return_wit_3 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z)  __default__Prod_Z_Z (PreH1 : (d_pre > (2 * h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) ,
  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  (“ ((-1) = (-1)) ” 
  &&  “ (Spec n_pre d_pre h_pre None ) ”
  &&  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) ))
  ||
  (EX (ev_data: (@list Z))  (eu_data: (@list Z))  (edges: (@list (Z * Z))) ,
  “ (Spec n_pre d_pre h_pre (Some (edges)) ) ” 
  &&  “ ((-1) = (Zlength (edges))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> (((Znth i eu_data 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i ev_data 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data ))
.

Definition solver_return_wit_4 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z)  __default__Prod_Z_Z (PreH1 : (n_pre > 2)) (PreH2 : (d_pre = 1)) (PreH3 : (d_pre >= h_pre)) (PreH4 : (d_pre <= (2 * h_pre ))) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (1 <= h_pre)) (PreH8 : (h_pre <= d_pre)) (PreH9 : (d_pre <= (n_pre - 1 ))) ,
  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) )
|--
  (“ ((-1) = (-1)) ” 
  &&  “ (Spec n_pre d_pre h_pre None ) ”
  &&  (IntArray.undef_full eu_pre (n_pre - 1 ) )
  **  (IntArray.undef_full ev_pre (n_pre - 1 ) ))
  ||
  (EX (ev_data: (@list Z))  (eu_data: (@list Z))  (edges: (@list (Z * Z))) ,
  “ (Spec n_pre d_pre h_pre (Some (edges)) ) ” 
  &&  “ ((-1) = (Zlength (edges))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (edges)))) -> (((Znth i eu_data 0) = (fst ((Znth i edges __default__Prod_Z_Z)))) /\ ((Znth i ev_data 0) = (snd ((Znth i edges __default__Prod_Z_Z)))))) ”
  &&  (IntArray.full eu_pre (Zlength (edges)) eu_data )
  **  (IntArray.full ev_pre (Zlength (edges)) ev_data ))
.

Definition solver_partial_solve_wit_1 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (i < h_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= h_pre) ” 
  &&  “ (count = i) ” 
  &&  “ (next = (i + 2 )) ” 
  &&  “ (last = (i + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((eu_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_2 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < h_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= h_pre)) (PreH10 : (count = i)) (PreH11 : (next = (i + 2 ))) (PreH12 : (last = (i + 1 ))) (PreH13 : ((Zlength (eu_data)) = count)) (PreH14 : ((Zlength (ev_data)) = count)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (i < h_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= h_pre) ” 
  &&  “ (count = i) ” 
  &&  “ (next = (i + 2 )) ” 
  &&  “ (last = (i + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((ev_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
.

Definition solver_partial_solve_wit_3 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (i < (d_pre - h_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (d_pre - h_pre )) ” 
  &&  “ (count = (h_pre + i )) ” 
  &&  “ (next = ((h_pre + i ) + 2 )) ” 
  &&  “ (0 < i) ” 
  &&  “ (last = ((h_pre + i ) + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((eu_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_4 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (i < (d_pre - h_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (d_pre - h_pre )) ” 
  &&  “ (count = (h_pre + i )) ” 
  &&  “ (next = ((h_pre + i ) + 2 )) ” 
  &&  “ (i = 0) ” 
  &&  “ (last = 1) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((eu_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_5 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (0 < i)) (PreH13 : (last = ((h_pre + i ) + 1 ))) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (i < (d_pre - h_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (d_pre - h_pre )) ” 
  &&  “ (count = (h_pre + i )) ” 
  &&  “ (next = ((h_pre + i ) + 2 )) ” 
  &&  “ (0 < i) ” 
  &&  “ (last = ((h_pre + i ) + 1 )) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((ev_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
.

Definition solver_partial_solve_wit_6 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (last: Z) (next: Z) (count: Z) (i: Z) (PreH1 : (i < (d_pre - h_pre ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (0 <= i)) (PreH9 : (i <= (d_pre - h_pre ))) (PreH10 : (count = (h_pre + i ))) (PreH11 : (next = ((h_pre + i ) + 2 ))) (PreH12 : (i = 0)) (PreH13 : (last = 1)) (PreH14 : ((Zlength (eu_data)) = count)) (PreH15 : ((Zlength (ev_data)) = count)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (i < (d_pre - h_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (d_pre - h_pre )) ” 
  &&  “ (count = (h_pre + i )) ” 
  &&  “ (next = ((h_pre + i ) + 2 )) ” 
  &&  “ (i = 0) ” 
  &&  “ (last = 1) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((ev_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (last) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
.

Definition solver_partial_solve_wit_7 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (next <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= count) ” 
  &&  “ (count <= (n_pre - 1 )) ” 
  &&  “ (next = (count + 2 )) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (last = 1) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (attach = 2) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((eu_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_8 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.undef_seg eu_pre count (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (next <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= count) ” 
  &&  “ (count <= (n_pre - 1 )) ” 
  &&  “ (next = (count + 2 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (last = (d_pre + 1 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (attach = 1) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((eu_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 count eu_data )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_9 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre = h_pre)) (PreH12 : (last = 1)) (PreH13 : (d_pre = h_pre)) (PreH14 : (attach = 2)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (next <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= count) ” 
  &&  “ (count <= (n_pre - 1 )) ” 
  &&  “ (next = (count + 2 )) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (last = 1) ” 
  &&  “ (d_pre = h_pre) ” 
  &&  “ (attach = 2) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((ev_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
.

Definition solver_partial_solve_wit_10 := 
forall (ev_pre: Z) (eu_pre: Z) (h_pre: Z) (d_pre: Z) (n_pre: Z) (ev_data: (@list Z)) (eu_data: (@list Z)) (attach: Z) (last: Z) (next: Z) (count: Z) (PreH1 : (next <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= h_pre)) (PreH5 : (h_pre <= d_pre)) (PreH6 : (d_pre <= (n_pre - 1 ))) (PreH7 : (Feasible n_pre d_pre h_pre )) (PreH8 : (d_pre <= count)) (PreH9 : (count <= (n_pre - 1 ))) (PreH10 : (next = (count + 2 ))) (PreH11 : (d_pre <> h_pre)) (PreH12 : (last = (d_pre + 1 ))) (PreH13 : (d_pre <> h_pre)) (PreH14 : (attach = 1)) (PreH15 : ((Zlength (eu_data)) = count)) (PreH16 : ((Zlength (ev_data)) = count)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) ))) ,
  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
  **  (IntArray.undef_seg ev_pre count (n_pre - 1 ) )
|--
  “ (next <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= h_pre) ” 
  &&  “ (h_pre <= d_pre) ” 
  &&  “ (d_pre <= (n_pre - 1 )) ” 
  &&  “ (Feasible n_pre d_pre h_pre ) ” 
  &&  “ (d_pre <= count) ” 
  &&  “ (count <= (n_pre - 1 )) ” 
  &&  “ (next = (count + 2 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (last = (d_pre + 1 )) ” 
  &&  “ (d_pre <> h_pre) ” 
  &&  “ (attach = 1) ” 
  &&  “ ((Zlength (eu_data)) = count) ” 
  &&  “ ((Zlength (ev_data)) = count) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < count)) -> (CanonicalEndpoints d_pre h_pre k (Znth k eu_data 0) (Znth k ev_data 0) )) ”
  &&  (((ev_pre + (count * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ev_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg eu_pre 0 (count + 1 ) (app (eu_data) ((cons (attach) ((@nil Z))))) )
  **  (IntArray.undef_seg eu_pre (count + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg ev_pre 0 count ev_data )
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
Axiom proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1.
Axiom proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
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
