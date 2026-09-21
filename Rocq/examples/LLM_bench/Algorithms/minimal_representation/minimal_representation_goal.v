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
Require Import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_lib.
Local Open Scope sac.

(*----- Function minimal_representation -----*)

Definition minimal_representation_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (0 <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "p" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "b" ) ) 2000 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((n_pre + p ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + p )) ”
.

Definition minimal_representation_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg ( &( "b" ) ) n_pre ((n_pre + p ) + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) ((n_pre + p ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition minimal_representation_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) p n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) p n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minimal_representation_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) p n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ False ”
.

Definition minimal_representation_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ False ”
.

Definition minimal_representation_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_11 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i <> j)) (PreH12 : (0 <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best )) (PreH15 : (MRCandidateState l best i j )) (PreH16 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition minimal_representation_safety_wit_12 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i <> j)) (PreH12 : (0 <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best )) (PreH15 : (MRCandidateState l best i j )) (PreH16 : (MRRotationPrefixEq l i j k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((i + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + k )) ”
.

Definition minimal_representation_safety_wit_13 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) = (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i <> j)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) (PreH17 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition minimal_representation_safety_wit_14 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k <> n_pre)) (PreH2 : (k >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i <> j)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) (PreH17 : (MRRotationPrefixEq l i j k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ False ”
.

Definition minimal_representation_safety_wit_15 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k = n_pre)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) (PreH18 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ False ”
.

Definition minimal_representation_safety_wit_16 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k <> n_pre)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) (PreH18 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition minimal_representation_safety_wit_17 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k <> n_pre)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) (PreH18 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((i + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + k )) ”
.

Definition minimal_representation_safety_wit_18 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) > (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k <> n_pre)) (PreH3 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (0 <= best)) (PreH9 : (best < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i <> j)) (PreH15 : (0 <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best )) (PreH18 : (MRCandidateState l best i j )) (PreH19 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (((i + k ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i + k ) + 1 )) ”
.

Definition minimal_representation_safety_wit_19 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) > (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k <> n_pre)) (PreH3 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (0 <= best)) (PreH9 : (best < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i <> j)) (PreH15 : (0 <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best )) (PreH18 : (MRCandidateState l best i j )) (PreH19 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((i + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + k )) ”
.

Definition minimal_representation_safety_wit_20 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) > (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k <> n_pre)) (PreH3 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (0 <= best)) (PreH9 : (best < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i <> j)) (PreH15 : (0 <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best )) (PreH18 : (MRCandidateState l best i j )) (PreH19 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minimal_representation_safety_wit_21 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (((i + k ) + 1 ) = j)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) > (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k <> n_pre)) (PreH4 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= best)) (PreH10 : (best < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i <> j)) (PreH16 : (0 <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best )) (PreH19 : (MRCandidateState l best i j )) (PreH20 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> ((i + k ) + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((((i + k ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i + k ) + 1 ) + 1 )) ”
.

Definition minimal_representation_safety_wit_22 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) <= (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k <> n_pre)) (PreH3 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (0 <= best)) (PreH9 : (best < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i <> j)) (PreH15 : (0 <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best )) (PreH18 : (MRCandidateState l best i j )) (PreH19 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (((j + k ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((j + k ) + 1 )) ”
.

Definition minimal_representation_safety_wit_23 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) <= (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k <> n_pre)) (PreH3 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (0 <= best)) (PreH9 : (best < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i <> j)) (PreH15 : (0 <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best )) (PreH18 : (MRCandidateState l best i j )) (PreH19 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((j + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + k )) ”
.

Definition minimal_representation_safety_wit_24 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) <= (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k <> n_pre)) (PreH3 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (0 <= best)) (PreH9 : (best < n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i < n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i <> j)) (PreH15 : (0 <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best )) (PreH18 : (MRCandidateState l best i j )) (PreH19 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition minimal_representation_safety_wit_25 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (i = ((j + k ) + 1 ))) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <= (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k <> n_pre)) (PreH4 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= best)) (PreH10 : (best < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i <> j)) (PreH16 : (0 <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best )) (PreH19 : (MRCandidateState l best i j )) (PreH20 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> ((j + k ) + 1 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ ((((j + k ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((j + k ) + 1 ) + 1 )) ”
.

Definition minimal_representation_safety_wit_26 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> i)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_27 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> i)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_28 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_29 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition minimal_representation_safety_wit_30 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre k n_pre )
|--
  “ ((best + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best + k )) ”
.

Definition minimal_representation_safety_wit_31 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (k) ((MRRotation (l) (best))))) ((cons ((Znth (best + k ) (app (l) (l)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (k + 1 ) n_pre )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition minimal_representation_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (0 <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.undef_full ( &( "b" ) ) 2000 )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 0 (sublist (0) (0) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) 0 n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + 0 ) (sublist (0) (0) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + 0 ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (0 <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.undef_full ( &( "b" ) ) 2000 )
|--
  “ ((sublist (0) (0) (l)) = (@nil Z)) ”
  &&  (IntArray.undef_seg ( &( "b" ) ) 0 n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + 0 ) (sublist (0) (0) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + 0 ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
).

Definition minimal_representation_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (0 <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.undef_full ( &( "b" ) ) 2000 )
|--
  “ ((sublist (0) (0) (l)) = (@nil Z)) ”
.

Definition minimal_representation_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (0 <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.undef_full ( &( "b" ) ) 2000 )
|--
  (IntArray.undef_seg ( &( "b" ) ) 0 n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + 0 ) (sublist (0) (0) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + 0 ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
.

Definition minimal_representation_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg ( &( "b" ) ) n_pre ((n_pre + p ) + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) ((n_pre + p ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (sublist (0) ((p + 1 )) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + (p + 1 ) ) (sublist (0) ((p + 1 )) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + (p + 1 ) ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg ( &( "b" ) ) n_pre ((n_pre + p ) + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
|--
  “ ((app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) = (sublist (0) ((p + 1 )) (l))) ”
  &&  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + (p + 1 ) ) (sublist (0) ((p + 1 )) (l)) )
).

Definition minimal_representation_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg ( &( "b" ) ) n_pre ((n_pre + p ) + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
|--
  “ ((app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) = (sublist (0) ((p + 1 )) (l))) ”
.

Definition minimal_representation_entail_wit_2_split_goal_spatial := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg ( &( "b" ) ) n_pre ((n_pre + p ) + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
|--
  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + (p + 1 ) ) (sublist (0) ((p + 1 )) (l)) )
.

Definition minimal_representation_entail_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "p" ) )) # Int  |-> p)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) p n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (2 * n_pre )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < (2 * n_pre )) ” 
  &&  “ (0 <> 1) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best 0 1 ) ”
  &&  ((( &( "p" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (2 * n_pre )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < (2 * n_pre )) ” 
  &&  “ (0 <> 1) ” 
  &&  “ (1 < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best 0 1 ) ”
  &&  ((( &( "p" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
.

Definition minimal_representation_entail_wit_4_1 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i j ) ” 
  &&  “ (MRRotationPrefixEq l i j 0 ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  TT && emp 
|--
  “ (MRRotationPrefixEq l i j 0 ) ”
  &&  emp
).

Definition minimal_representation_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  (MRRotationPrefixEq l i j 0 )
.

Definition minimal_representation_entail_wit_4_2 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i j ) ” 
  &&  “ (MRRotationPrefixEq l i j 0 ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  TT && emp 
|--
  “ (MRRotationPrefixEq l i j 0 ) ”
  &&  emp
).

Definition minimal_representation_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (j < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  (MRRotationPrefixEq l i j 0 )
.

Definition minimal_representation_entail_wit_5 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) = (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i <> j)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) (PreH17 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i j ) ” 
  &&  “ (MRRotationPrefixEq l i j (k + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) = (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i <> j)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) (PreH17 : (MRRotationPrefixEq l i j k )) ,
  TT && emp 
|--
  “ (MRRotationPrefixEq l i j (k + 1 ) ) ”
  &&  emp
).

Definition minimal_representation_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : ((Znth (i + k ) (app (l) (l)) 0) = (Znth (j + k ) (app (l) (l)) 0))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i <> j)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) (PreH17 : (MRRotationPrefixEq l i j k )) ,
  (MRRotationPrefixEq l i j (k + 1 ) )
.

Definition minimal_representation_entail_wit_6_1 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (((i + k ) + 1 ) = j)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) > (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k <> n_pre)) (PreH4 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= best)) (PreH10 : (best < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i <> j)) (PreH16 : (0 <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best )) (PreH19 : (MRCandidateState l best i j )) (PreH20 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= (((i + k ) + 1 ) + 1 )) ” 
  &&  “ ((((i + k ) + 1 ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ ((((i + k ) + 1 ) + 1 ) <> j) ” 
  &&  “ ((((i + k ) + 1 ) + 1 ) < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best (((i + k ) + 1 ) + 1 ) j ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= (((i + k ) + 1 ) + 1 )) ” 
  &&  “ ((((i + k ) + 1 ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ ((((i + k ) + 1 ) + 1 ) <> j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best (((i + k ) + 1 ) + 1 ) j ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
.

Definition minimal_representation_entail_wit_6_2 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (((i + k ) + 1 ) <> j)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) > (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k <> n_pre)) (PreH4 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= best)) (PreH10 : (best < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i <> j)) (PreH16 : (0 <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best )) (PreH19 : (MRCandidateState l best i j )) (PreH20 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= ((i + k ) + 1 )) ” 
  &&  “ (((i + k ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (((i + k ) + 1 ) <> j) ” 
  &&  “ (((i + k ) + 1 ) < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best ((i + k ) + 1 ) j ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= ((i + k ) + 1 )) ” 
  &&  “ (((i + k ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (((i + k ) + 1 ) <> j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best ((i + k ) + 1 ) j ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
.

Definition minimal_representation_entail_wit_6_3 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (i = ((j + k ) + 1 ))) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <= (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k <> n_pre)) (PreH4 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= best)) (PreH10 : (best < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i <> j)) (PreH16 : (0 <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best )) (PreH19 : (MRCandidateState l best i j )) (PreH20 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= (((j + k ) + 1 ) + 1 )) ” 
  &&  “ ((((j + k ) + 1 ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (i <> (((j + k ) + 1 ) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i (((j + k ) + 1 ) + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= (((j + k ) + 1 ) + 1 )) ” 
  &&  “ ((((j + k ) + 1 ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (i <> (((j + k ) + 1 ) + 1 )) ” 
  &&  “ ((((j + k ) + 1 ) + 1 ) < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i (((j + k ) + 1 ) + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
.

Definition minimal_representation_entail_wit_6_4 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (i <> ((j + k ) + 1 ))) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <= (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k <> n_pre)) (PreH4 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= best)) (PreH10 : (best < n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i <> j)) (PreH16 : (0 <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best )) (PreH19 : (MRCandidateState l best i j )) (PreH20 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= ((j + k ) + 1 )) ” 
  &&  “ (((j + k ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (i <> ((j + k ) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i ((j + k ) + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= ((j + k ) + 1 )) ” 
  &&  “ (((j + k ) + 1 ) < (2 * n_pre )) ” 
  &&  “ (i <> ((j + k ) + 1 )) ” 
  &&  “ (((j + k ) + 1 ) < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i ((j + k ) + 1 ) ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
.

Definition minimal_representation_entail_wit_7_1 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i < j) -> (i = best)) ” 
  &&  “ ((i >= j) -> (j = best)) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) ,
  TT && emp 
|--
  “ ((i >= j) -> (j = best)) ”
  &&  emp
).

Definition minimal_representation_entail_wit_7_1_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) ,
  ((i >= j) -> (j = best))
.

Definition minimal_representation_entail_wit_7_2 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i < j) -> (i = best)) ” 
  &&  “ ((i >= j) -> (j = best)) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  TT && emp 
|--
  “ ((i < j) -> (i = best)) ”
  &&  emp
).

Definition minimal_representation_entail_wit_7_2_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < (2 * n_pre ))) (PreH10 : (0 <= j)) (PreH11 : (j < (2 * n_pre ))) (PreH12 : (i <> j)) (PreH13 : (i < n_pre)) (PreH14 : (0 <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) ,
  ((i < j) -> (i = best))
.

Definition minimal_representation_entail_wit_7_3 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k = n_pre)) (PreH2 : (k >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= best)) (PreH7 : (best < n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i <> j)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best )) (PreH16 : (MRCandidateState l best i j )) (PreH17 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i < j) -> (i = best)) ” 
  &&  “ ((i >= j) -> (j = best)) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i < j) -> (i = best)) ” 
  &&  “ ((i >= j) -> (j = best)) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre ))
.

Definition minimal_representation_entail_wit_8_1 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "p" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  ((( &( "p" ) )) # Int  |-> best)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 0 (sublist (0) (0) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  TT && emp 
|--
  “ ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z)) ”
  &&  emp
).

Definition minimal_representation_entail_wit_8_1_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z))
.

Definition minimal_representation_entail_wit_8_2 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "p" ) )) # Int  |-> i)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  ((( &( "p" ) )) # Int  |-> best)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 0 (sublist (0) (0) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  TT && emp 
|--
  “ ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z)) ”
  &&  emp
).

Definition minimal_representation_entail_wit_8_2_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z))
.

Definition minimal_representation_entail_wit_8_3 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "p" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  ((( &( "p" ) )) # Int  |-> best)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 0 (sublist (0) (0) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  TT && emp 
|--
  “ ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z)) ”
  &&  emp
).

Definition minimal_representation_entail_wit_8_3_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (j < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z))
.

Definition minimal_representation_entail_wit_8_4 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((( &( "p" ) )) # Int  |-> j)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  ((( &( "p" ) )) # Int  |-> best)
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 0 (sublist (0) (0) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  TT && emp 
|--
  “ ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z)) ”
  &&  emp
).

Definition minimal_representation_entail_wit_8_4_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < (2 * n_pre ))) (PreH9 : (0 <= j)) (PreH10 : (j < (2 * n_pre ))) (PreH11 : (i <> j)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best )) ,
  ((sublist (0) (0) ((MRRotation (l) (best)))) = (@nil Z))
.

Definition minimal_representation_entail_wit_9 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg out_pre 0 (k + 1 ) (app ((sublist (0) (k) ((MRRotation (l) (best))))) ((cons ((Znth (best + k ) (app (l) (l)) 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (k + 1 ) n_pre )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 (k + 1 ) (sublist (0) ((k + 1 )) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre (k + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (k) ((MRRotation (l) (best))))) ((cons ((Znth (best + k ) (app (l) (l)) 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) ((MRRotation (l) (best))))) ”
  &&  emp
).

Definition minimal_representation_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  ((app ((sublist (0) (k) ((MRRotation (l) (best))))) ((cons ((Znth (best + k ) (app (l) (l)) 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) ((MRRotation (l) (best)))))
.

Definition minimal_representation_entail_wit_10 := 
(
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre k n_pre )
|--
  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= k) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full out_pre n_pre (MRRotation (l) (best)) )
  **  (IntArray.undef_full ( &( "b" ) ) 2000 )
) \/
(
forall (out_pre: Z) (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
|--
  (IntArray.full out_pre n_pre (MRRotation (l) (best)) )
  **  (IntArray.undef_full ( &( "b" ) ) 2000 )
).

Definition minimal_representation_entail_wit_10_split_goal_spatial := 
forall (out_pre: Z) (n_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
|--
  (IntArray.full out_pre n_pre (MRRotation (l) (best)) )
  **  (IntArray.undef_full ( &( "b" ) ) 2000 )
.

Definition minimal_representation_return_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) (j: Z) (k: Z) (p: Z) (PreH1 : (0 <= i)) (PreH2 : (0 <= j)) (PreH3 : (0 <= k)) (PreH4 : (MRFirstMinimalRotationAt l p )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full out_pre n_pre (MRRotation (l) (p)) )
|--
  “ (MRFirstMinimalRotationAt l p ) ”
  &&  (IntArray.full a_pre n_pre l )
  **  (IntArray.full out_pre n_pre (MRRotation (l) (p)) )
.

Definition minimal_representation_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) p n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (p < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (((a_pre + (p * sizeof(INT)))) # Int  |-> (Znth p l 0))
  **  (IntArray.missing_i a_pre p 0 n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) p n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) p n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (p < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (((( &( "b" ) ) + (p * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 p (sublist (0) (p) (l)) )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (p < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (((a_pre + (p * sizeof(INT)))) # Int  |-> (Znth p l 0))
  **  (IntArray.missing_i a_pre p 0 n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (p: Z) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (n_pre + p ) (2 * n_pre ) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (p < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (((( &( "b" ) ) + ((n_pre + p ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "b" ) ) ((n_pre + p ) + 1 ) (2 * n_pre ) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.seg ( &( "b" ) ) 0 (p + 1 ) (app ((sublist (0) (p) (l))) ((cons ((Znth p l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "b" ) ) (p + 1 ) n_pre )
  **  (IntArray.seg ( &( "b" ) ) n_pre (n_pre + p ) (sublist (0) (p) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i <> j)) (PreH12 : (0 <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best )) (PreH15 : (MRCandidateState l best i j )) (PreH16 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i j ) ” 
  &&  “ (MRRotationPrefixEq l i j k ) ”
  &&  (((( &( "b" ) ) + ((i + k ) * sizeof(INT)))) # Int  |-> (Znth (i + k ) (app (l) (l)) 0))
  **  (IntArray.missing_i ( &( "b" ) ) (i + k ) 0 (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i <> j)) (PreH12 : (0 <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best )) (PreH15 : (MRCandidateState l best i j )) (PreH16 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i j ) ” 
  &&  “ (MRRotationPrefixEq l i j k ) ”
  &&  (((( &( "b" ) ) + ((j + k ) * sizeof(INT)))) # Int  |-> (Znth (j + k ) (app (l) (l)) 0))
  **  (IntArray.missing_i ( &( "b" ) ) (j + k ) 0 (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k <> n_pre)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) (PreH18 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (k <> n_pre) ” 
  &&  “ ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0)) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i j ) ” 
  &&  “ (MRRotationPrefixEq l i j k ) ”
  &&  (((( &( "b" ) ) + ((i + k ) * sizeof(INT)))) # Int  |-> (Znth (i + k ) (app (l) (l)) 0))
  **  (IntArray.missing_i ( &( "b" ) ) (i + k ) 0 (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k <> n_pre)) (PreH2 : ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) (PreH17 : (MRCandidateState l best i j )) (PreH18 : (MRRotationPrefixEq l i j k )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (k <> n_pre) ” 
  &&  “ ((Znth (i + k ) (app (l) (l)) 0) <> (Znth (j + k ) (app (l) (l)) 0)) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ” 
  &&  “ (MRCandidateState l best i j ) ” 
  &&  “ (MRRotationPrefixEq l i j k ) ”
  &&  (((( &( "b" ) ) + ((j + k ) * sizeof(INT)))) # Int  |-> (Znth (j + k ) (app (l) (l)) 0))
  **  (IntArray.missing_i ( &( "b" ) ) (j + k ) 0 (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.undef_full out_pre n_pre )
.

Definition minimal_representation_partial_solve_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full a_pre n_pre l )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre k n_pre )
|--
  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (((( &( "b" ) ) + ((best + k ) * sizeof(INT)))) # Int  |-> (Znth (best + k ) (app (l) (l)) 0))
  **  (IntArray.missing_i ( &( "b" ) ) (best + k ) 0 (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre k n_pre )
.

Definition minimal_representation_partial_solve_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (a_pre: Z) (best: Z) (l: (@list Z)) (k: Z) (j: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (0 <= best)) (PreH6 : (best < n_pre)) (PreH7 : (0 <= best)) (PreH8 : (best < n_pre)) (PreH9 : (0 <= i)) (PreH10 : (i < (2 * n_pre ))) (PreH11 : (0 <= j)) (PreH12 : (j < (2 * n_pre ))) (PreH13 : (i <> j)) (PreH14 : (0 <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best )) ,
  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
  **  (IntArray.undef_seg out_pre k n_pre )
|--
  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (2 * n_pre )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (2 * n_pre )) ” 
  &&  “ (i <> j) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (MRFirstMinimalRotationAt l best ) ”
  &&  (((out_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (k + 1 ) n_pre )
  **  (IntArray.full ( &( "b" ) ) (2 * n_pre ) (app (l) (l)) )
  **  (IntArray.full a_pre n_pre l )
  **  (IntArray.undef_seg ( &( "b" ) ) (2 * n_pre ) 2000 )
  **  (IntArray.seg out_pre 0 k (sublist (0) (k) ((MRRotation (l) (best)))) )
.

Module Type VC_Correct.


Axiom proof_of_minimal_representation_safety_wit_1 : minimal_representation_safety_wit_1.
Axiom proof_of_minimal_representation_safety_wit_2 : minimal_representation_safety_wit_2.
Axiom proof_of_minimal_representation_safety_wit_3 : minimal_representation_safety_wit_3.
Axiom proof_of_minimal_representation_safety_wit_4 : minimal_representation_safety_wit_4.
Axiom proof_of_minimal_representation_safety_wit_5 : minimal_representation_safety_wit_5.
Axiom proof_of_minimal_representation_safety_wit_6 : minimal_representation_safety_wit_6.
Axiom proof_of_minimal_representation_safety_wit_7 : minimal_representation_safety_wit_7.
Axiom proof_of_minimal_representation_safety_wit_8 : minimal_representation_safety_wit_8.
Axiom proof_of_minimal_representation_safety_wit_9 : minimal_representation_safety_wit_9.
Axiom proof_of_minimal_representation_safety_wit_10 : minimal_representation_safety_wit_10.
Axiom proof_of_minimal_representation_safety_wit_11 : minimal_representation_safety_wit_11.
Axiom proof_of_minimal_representation_safety_wit_12 : minimal_representation_safety_wit_12.
Axiom proof_of_minimal_representation_safety_wit_13 : minimal_representation_safety_wit_13.
Axiom proof_of_minimal_representation_safety_wit_14 : minimal_representation_safety_wit_14.
Axiom proof_of_minimal_representation_safety_wit_15 : minimal_representation_safety_wit_15.
Axiom proof_of_minimal_representation_safety_wit_16 : minimal_representation_safety_wit_16.
Axiom proof_of_minimal_representation_safety_wit_17 : minimal_representation_safety_wit_17.
Axiom proof_of_minimal_representation_safety_wit_18 : minimal_representation_safety_wit_18.
Axiom proof_of_minimal_representation_safety_wit_19 : minimal_representation_safety_wit_19.
Axiom proof_of_minimal_representation_safety_wit_20 : minimal_representation_safety_wit_20.
Axiom proof_of_minimal_representation_safety_wit_21 : minimal_representation_safety_wit_21.
Axiom proof_of_minimal_representation_safety_wit_22 : minimal_representation_safety_wit_22.
Axiom proof_of_minimal_representation_safety_wit_23 : minimal_representation_safety_wit_23.
Axiom proof_of_minimal_representation_safety_wit_24 : minimal_representation_safety_wit_24.
Axiom proof_of_minimal_representation_safety_wit_25 : minimal_representation_safety_wit_25.
Axiom proof_of_minimal_representation_safety_wit_26 : minimal_representation_safety_wit_26.
Axiom proof_of_minimal_representation_safety_wit_27 : minimal_representation_safety_wit_27.
Axiom proof_of_minimal_representation_safety_wit_28 : minimal_representation_safety_wit_28.
Axiom proof_of_minimal_representation_safety_wit_29 : minimal_representation_safety_wit_29.
Axiom proof_of_minimal_representation_safety_wit_30 : minimal_representation_safety_wit_30.
Axiom proof_of_minimal_representation_safety_wit_31 : minimal_representation_safety_wit_31.
Axiom proof_of_minimal_representation_entail_wit_1 : minimal_representation_entail_wit_1.
Axiom proof_of_minimal_representation_entail_wit_2 : minimal_representation_entail_wit_2.
Axiom proof_of_minimal_representation_entail_wit_3 : minimal_representation_entail_wit_3.
Axiom proof_of_minimal_representation_entail_wit_4_1 : minimal_representation_entail_wit_4_1.
Axiom proof_of_minimal_representation_entail_wit_4_2 : minimal_representation_entail_wit_4_2.
Axiom proof_of_minimal_representation_entail_wit_5 : minimal_representation_entail_wit_5.
Axiom proof_of_minimal_representation_entail_wit_6_1 : minimal_representation_entail_wit_6_1.
Axiom proof_of_minimal_representation_entail_wit_6_2 : minimal_representation_entail_wit_6_2.
Axiom proof_of_minimal_representation_entail_wit_6_3 : minimal_representation_entail_wit_6_3.
Axiom proof_of_minimal_representation_entail_wit_6_4 : minimal_representation_entail_wit_6_4.
Axiom proof_of_minimal_representation_entail_wit_7_1 : minimal_representation_entail_wit_7_1.
Axiom proof_of_minimal_representation_entail_wit_7_2 : minimal_representation_entail_wit_7_2.
Axiom proof_of_minimal_representation_entail_wit_7_3 : minimal_representation_entail_wit_7_3.
Axiom proof_of_minimal_representation_entail_wit_8_1 : minimal_representation_entail_wit_8_1.
Axiom proof_of_minimal_representation_entail_wit_8_2 : minimal_representation_entail_wit_8_2.
Axiom proof_of_minimal_representation_entail_wit_8_3 : minimal_representation_entail_wit_8_3.
Axiom proof_of_minimal_representation_entail_wit_8_4 : minimal_representation_entail_wit_8_4.
Axiom proof_of_minimal_representation_entail_wit_9 : minimal_representation_entail_wit_9.
Axiom proof_of_minimal_representation_entail_wit_10 : minimal_representation_entail_wit_10.
Axiom proof_of_minimal_representation_return_wit_1 : minimal_representation_return_wit_1.
Axiom proof_of_minimal_representation_partial_solve_wit_1 : minimal_representation_partial_solve_wit_1.
Axiom proof_of_minimal_representation_partial_solve_wit_2 : minimal_representation_partial_solve_wit_2.
Axiom proof_of_minimal_representation_partial_solve_wit_3 : minimal_representation_partial_solve_wit_3.
Axiom proof_of_minimal_representation_partial_solve_wit_4 : minimal_representation_partial_solve_wit_4.
Axiom proof_of_minimal_representation_partial_solve_wit_5 : minimal_representation_partial_solve_wit_5.
Axiom proof_of_minimal_representation_partial_solve_wit_6 : minimal_representation_partial_solve_wit_6.
Axiom proof_of_minimal_representation_partial_solve_wit_7 : minimal_representation_partial_solve_wit_7.
Axiom proof_of_minimal_representation_partial_solve_wit_8 : minimal_representation_partial_solve_wit_8.
Axiom proof_of_minimal_representation_partial_solve_wit_9 : minimal_representation_partial_solve_wit_9.
Axiom proof_of_minimal_representation_partial_solve_wit_10 : minimal_representation_partial_solve_wit_10.

End VC_Correct.
