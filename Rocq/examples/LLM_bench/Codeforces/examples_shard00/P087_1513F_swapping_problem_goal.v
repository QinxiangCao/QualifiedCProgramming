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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P087_1513F_swapping_problem_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P087_1513F_swapping_problem_lib.
Local Open Scope sac.

(*----- Function cmp -----*)

(*----- Function overlap -----*)

Definition overlap_safety_wit_1 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (na_pre = 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 <= na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 <= nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (SegmentsBounded left )) (PreH9 : (SegmentsBounded right )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition overlap_safety_wit_2 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre = 0)) (PreH2 : (na_pre <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 <= na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 <= nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (SegmentsBounded left )) (PreH10 : (SegmentsBounded right )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition overlap_safety_wit_3 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Zlength (sorted)) = nb_pre)) (PreH3 : (Permutation right sorted )) (PreH4 : (SegmentsBounded sorted )) (PreH5 : (SegmentsSortedByLeft sorted )) (PreH6 : (nb_pre <> 0)) (PreH7 : (na_pre <> 0)) (PreH8 : (na_pre = (Zlength (left)))) (PreH9 : (nb_pre = (Zlength (right)))) (PreH10 : (0 <= na_pre)) (PreH11 : (na_pre <= 200000)) (PreH12 : (0 <= nb_pre)) (PreH13 : (nb_pre <= 200000)) (PreH14 : (SegmentsBounded left )) (PreH15 : (SegmentsBounded right )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval nb_pre )
  **  ((( &( "pref" ) )) # Ptr  |-> retval)
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition overlap_safety_wit_4 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix 0) > (snd ((Znth i sorted __default__Prod_Z_Z))))) (PreH2 : (i <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < nb_pre)) (PreH11 : ((Zlength (prefix)) = i)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : (SegmentsBounded left )) (PreH14 : (Permutation right sorted )) (PreH15 : (SegmentsBounded sorted )) (PreH16 : (SegmentsSortedByLeft sorted )) (PreH17 : (PrefixRightMaxima sorted prefix i )) ,
  (IntArray.full pref i prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) prefix 0))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_safety_wit_5 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (i = 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < nb_pre)) (PreH10 : ((Zlength (prefix)) = i)) (PreH11 : ((Zlength (sorted)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted )) (PreH14 : (SegmentsBounded sorted )) (PreH15 : (SegmentsSortedByLeft sorted )) (PreH16 : (PrefixRightMaxima sorted prefix i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref i prefix )
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_safety_wit_6 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix 0) <= (snd ((Znth i sorted __default__Prod_Z_Z))))) (PreH2 : (i <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < nb_pre)) (PreH11 : ((Zlength (prefix)) = i)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : (SegmentsBounded left )) (PreH14 : (Permutation right sorted )) (PreH15 : (SegmentsBounded sorted )) (PreH16 : (SegmentsSortedByLeft sorted )) (PreH17 : (PrefixRightMaxima sorted prefix i )) ,
  (IntArray.full pref i prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_safety_wit_7 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix 0) > (snd ((Znth i sorted __default__Prod_Z_Z))))) (PreH2 : (i <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < nb_pre)) (PreH11 : ((Zlength (prefix)) = i)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : (SegmentsBounded left )) (PreH14 : (Permutation right sorted )) (PreH15 : (SegmentsBounded sorted )) (PreH16 : (SegmentsSortedByLeft sorted )) (PreH17 : (PrefixRightMaxima sorted prefix i )) ,
  (IntArray.full pref i prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition overlap_safety_wit_8 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (i <> 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < nb_pre)) (PreH10 : ((Zlength (prefix)) = i)) (PreH11 : ((Zlength (sorted)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted )) (PreH14 : (SegmentsBounded sorted )) (PreH15 : (SegmentsSortedByLeft sorted )) (PreH16 : (PrefixRightMaxima sorted prefix i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref i prefix )
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition overlap_safety_wit_9 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (i <> 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < nb_pre)) (PreH10 : ((Zlength (prefix)) = i)) (PreH11 : ((Zlength (sorted)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted )) (PreH14 : (SegmentsBounded sorted )) (PreH15 : (SegmentsSortedByLeft sorted )) (PreH16 : (PrefixRightMaxima sorted prefix i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref i prefix )
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition overlap_safety_wit_10 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix 0) > (snd ((Znth i sorted __default__Prod_Z_Z))))) (PreH2 : (i <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < nb_pre)) (PreH11 : ((Zlength (prefix)) = i)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : (SegmentsBounded left )) (PreH14 : (Permutation right sorted )) (PreH15 : (SegmentsBounded sorted )) (PreH16 : (SegmentsSortedByLeft sorted )) (PreH17 : (PrefixRightMaxima sorted prefix i )) ,
  (IntArray.full pref i prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition overlap_safety_wit_11 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (PreH1 : (i >= nb_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= nb_pre)) (PreH10 : ((Zlength (prefix)) = i)) (PreH11 : ((Zlength (sorted)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted )) (PreH14 : (SegmentsBounded sorted )) (PreH15 : (SegmentsSortedByLeft sorted )) (PreH16 : (PrefixRightMaxima sorted prefix i )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref i prefix )
  **  (IntArray.undef_full (pref + (i * sizeof(INT))) (nb_pre - i ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition overlap_safety_wit_12 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (PreH1 : (i >= nb_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= nb_pre)) (PreH10 : ((Zlength (prefix)) = i)) (PreH11 : ((Zlength (sorted)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted )) (PreH14 : (SegmentsBounded sorted )) (PreH15 : (SegmentsSortedByLeft sorted )) (PreH16 : (PrefixRightMaxima sorted prefix i )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref i prefix )
  **  (IntArray.undef_full (pref + (i * sizeof(INT))) (nb_pre - i ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition overlap_safety_wit_13 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (i: Z) (PreH1 : (i < na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : ((Zlength (prefix)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted )) (PreH16 : (SegmentsBounded sorted )) (PreH17 : (SegmentsSortedByLeft sorted )) (PreH18 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition overlap_safety_wit_14 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (hi: Z) (lo: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (lo < hi)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  ((( &( "md" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ (((lo + hi ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition overlap_safety_wit_15 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (hi: Z) (lo: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (lo < hi)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  ((( &( "md" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ ((lo + hi ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + hi )) ”
.

Definition overlap_safety_wit_16 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (hi: Z) (lo: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (lo < hi)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  ((( &( "md" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition overlap_safety_wit_17 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (md: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((fst ((Znth md sorted __default__Prod_Z_Z))) <= (fst ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= md)) (PreH12 : (md < hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted)) = nb_pre)) (PreH17 : ((Zlength (prefix)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted )) (PreH20 : (SegmentsBounded sorted )) (PreH21 : (SegmentsSortedByLeft sorted )) (PreH22 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "md" ) )) # Int  |-> md)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre md (sublist (0) (md) (sorted)) )
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth md sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth md sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((md + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - md ) - 1 ) (sublist ((md + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ ((md + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (md + 1 )) ”
.

Definition overlap_safety_wit_18 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (md: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((fst ((Znth md sorted __default__Prod_Z_Z))) <= (fst ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= md)) (PreH12 : (md < hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted)) = nb_pre)) (PreH17 : ((Zlength (prefix)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted )) (PreH20 : (SegmentsBounded sorted )) (PreH21 : (SegmentsSortedByLeft sorted )) (PreH22 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "md" ) )) # Int  |-> md)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre md (sublist (0) (md) (sorted)) )
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth md sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth md sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((md + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - md ) - 1 ) (sublist ((md + 1 )) (nb_pre) (sorted)) )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition overlap_safety_wit_19 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((lo - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo - 1 )) ”
.

Definition overlap_safety_wit_20 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (na_pre = (Zlength (left)))) (PreH2 : (nb_pre = (Zlength (right)))) (PreH3 : (0 < na_pre)) (PreH4 : (na_pre <= 200000)) (PreH5 : (0 < nb_pre)) (PreH6 : (nb_pre <= 200000)) (PreH7 : (0 <= i)) (PreH8 : (i < na_pre)) (PreH9 : (0 <= lo)) (PreH10 : (lo = hi)) (PreH11 : (hi <= nb_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= 1000000000)) (PreH14 : ((Zlength (sorted)) = nb_pre)) (PreH15 : ((Zlength (prefix)) = nb_pre)) (PreH16 : (SegmentsBounded left )) (PreH17 : (Permutation right sorted )) (PreH18 : (SegmentsBounded sorted )) (PreH19 : (SegmentsSortedByLeft sorted )) (PreH20 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH21 : (DirectedOverlapMaximumPrefix left right i best )) (PreH22 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH23 : (lo <> 0)) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ ((lo - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo - 1 )) ”
.

Definition overlap_safety_wit_21 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (na_pre = (Zlength (left)))) (PreH2 : (nb_pre = (Zlength (right)))) (PreH3 : (0 < na_pre)) (PreH4 : (na_pre <= 200000)) (PreH5 : (0 < nb_pre)) (PreH6 : (nb_pre <= 200000)) (PreH7 : (0 <= i)) (PreH8 : (i < na_pre)) (PreH9 : (0 <= lo)) (PreH10 : (lo = hi)) (PreH11 : (hi <= nb_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= 1000000000)) (PreH14 : ((Zlength (sorted)) = nb_pre)) (PreH15 : ((Zlength (prefix)) = nb_pre)) (PreH16 : (SegmentsBounded left )) (PreH17 : (Permutation right sorted )) (PreH18 : (SegmentsBounded sorted )) (PreH19 : (SegmentsSortedByLeft sorted )) (PreH20 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH21 : (DirectedOverlapMaximumPrefix left right i best )) (PreH22 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH23 : (lo <> 0)) ,
  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition overlap_safety_wit_22 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition overlap_safety_wit_23 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (Znth (lo - 1 ) prefix 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) )) ”
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (Znth (lo - 1 ) prefix 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) )) ”
).

Definition overlap_safety_wit_23_split_goal_1 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (Znth (lo - 1 ) prefix 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= INT_MAX) ”
.

Definition overlap_safety_wit_23_split_goal_2 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (Znth (lo - 1 ) prefix 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT_MIN) <= ((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) )) ”
.

Definition overlap_safety_wit_24 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) )) ”
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) )) ”
).

Definition overlap_safety_wit_24_split_goal_1 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= INT_MAX) ”
.

Definition overlap_safety_wit_24_split_goal_2 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "x" ) )) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((INT_MIN) <= ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) )) ”
.

Definition overlap_safety_wit_25 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) > best)) (PreH2 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted)) = nb_pre)) (PreH17 : ((Zlength (prefix)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted )) (PreH20 : (SegmentsBounded sorted )) (PreH21 : (SegmentsSortedByLeft sorted )) (PreH22 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> ((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) ))
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_safety_wit_26 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) > best)) (PreH2 : ((Znth (lo - 1 ) prefix 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted)) = nb_pre)) (PreH17 : ((Zlength (prefix)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted )) (PreH20 : (SegmentsBounded sorted )) (PreH21 : (SegmentsSortedByLeft sorted )) (PreH22 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ))
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_safety_wit_27 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((Znth (lo - 1 ) prefix 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= best)) (PreH2 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted)) = nb_pre)) (PreH17 : ((Zlength (prefix)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted )) (PreH20 : (SegmentsBounded sorted )) (PreH21 : (SegmentsSortedByLeft sorted )) (PreH22 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_safety_wit_28 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= best)) (PreH2 : ((Znth (lo - 1 ) prefix 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted)) = nb_pre)) (PreH17 : ((Zlength (prefix)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted )) (PreH20 : (SegmentsBounded sorted )) (PreH21 : (SegmentsSortedByLeft sorted )) (PreH22 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_safety_wit_29 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (na_pre = (Zlength (left)))) (PreH2 : (nb_pre = (Zlength (right)))) (PreH3 : (0 < na_pre)) (PreH4 : (na_pre <= 200000)) (PreH5 : (0 < nb_pre)) (PreH6 : (nb_pre <= 200000)) (PreH7 : (0 <= i)) (PreH8 : (i < na_pre)) (PreH9 : (0 <= lo)) (PreH10 : (lo = hi)) (PreH11 : (hi <= nb_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= 1000000000)) (PreH14 : ((Zlength (sorted)) = nb_pre)) (PreH15 : ((Zlength (prefix)) = nb_pre)) (PreH16 : (SegmentsBounded left )) (PreH17 : (Permutation right sorted )) (PreH18 : (SegmentsBounded sorted )) (PreH19 : (SegmentsSortedByLeft sorted )) (PreH20 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH21 : (DirectedOverlapMaximumPrefix left right i best )) (PreH22 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH23 : (lo = 0)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition overlap_entail_wit_1 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Zlength (sorted_2)) = nb_pre)) (PreH3 : (Permutation right sorted_2 )) (PreH4 : (SegmentsBounded sorted_2 )) (PreH5 : (SegmentsSortedByLeft sorted_2 )) (PreH6 : (nb_pre <> 0)) (PreH7 : (na_pre <> 0)) (PreH8 : (na_pre = (Zlength (left)))) (PreH9 : (nb_pre = (Zlength (right)))) (PreH10 : (0 <= na_pre)) (PreH11 : (na_pre <= 200000)) (PreH12 : (0 <= nb_pre)) (PreH13 : (nb_pre <= 200000)) (PreH14 : (SegmentsBounded left )) (PreH15 : (SegmentsBounded right )) ,
  (IntArray.undef_full retval nb_pre )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (SegArray.full a_pre na_pre left )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nb_pre) ” 
  &&  “ ((Zlength (prefix)) = 0) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix 0 ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full retval 0 prefix )
  **  (IntArray.undef_full (retval + (0 * sizeof(INT))) (nb_pre - 0 ) )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : ((Zlength (sorted_2)) = nb_pre)) (PreH3 : (Permutation right sorted_2 )) (PreH4 : (SegmentsBounded sorted_2 )) (PreH5 : (SegmentsSortedByLeft sorted_2 )) (PreH6 : (nb_pre <> 0)) (PreH7 : (na_pre <> 0)) (PreH8 : (na_pre = (Zlength (left)))) (PreH9 : (nb_pre = (Zlength (right)))) (PreH10 : (0 <= na_pre)) (PreH11 : (na_pre <= 200000)) (PreH12 : (0 <= nb_pre)) (PreH13 : (nb_pre <= 200000)) (PreH14 : (SegmentsBounded left )) (PreH15 : (SegmentsBounded right )) ,
  (IntArray.undef_full retval nb_pre )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (SegArray.full a_pre na_pre left )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nb_pre) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted (@nil Z) 0 ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.undef_full (retval + (0 * sizeof(INT))) (nb_pre - 0 ) )
).

Definition overlap_entail_wit_2 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nb_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= nb_pre)) (PreH10 : ((Zlength (prefix_2)) = i)) (PreH11 : ((Zlength (sorted_2)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted_2 )) (PreH14 : (SegmentsBounded sorted_2 )) (PreH15 : (SegmentsSortedByLeft sorted_2 )) (PreH16 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.full pref i prefix_2 )
  **  (IntArray.undef_full (pref + (i * sizeof(INT))) (nb_pre - i ) )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nb_pre) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix i ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  (IntArray.full pref i prefix )
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < nb_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= nb_pre)) (PreH10 : ((Zlength (prefix_2)) = i)) (PreH11 : ((Zlength (sorted_2)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted_2 )) (PreH14 : (SegmentsBounded sorted_2 )) (PreH15 : (SegmentsSortedByLeft sorted_2 )) (PreH16 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.undef_full (pref + (i * sizeof(INT))) (nb_pre - i ) )
|--
  EX (x: Z)  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = i) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 i ) ”
  &&  (((pref + (i * sizeof(INT)))) # Int  |-> x)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
).

Definition overlap_entail_wit_3_1 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix_2 0) > (snd ((Znth i sorted_2 __default__Prod_Z_Z))))) (PreH2 : (i <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < nb_pre)) (PreH11 : ((Zlength (prefix_2)) = i)) (PreH12 : ((Zlength (sorted_2)) = nb_pre)) (PreH13 : (SegmentsBounded left )) (PreH14 : (Permutation right sorted_2 )) (PreH15 : (SegmentsBounded sorted_2 )) (PreH16 : (SegmentsSortedByLeft sorted_2 )) (PreH17 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (IntArray.full pref i prefix_2 )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted_2)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted_2)) )
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) prefix_2 0))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb_pre) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix (i + 1 ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref (i + 1 ) prefix )
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) (nb_pre - (i + 1 ) ) )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix_2 0) <= INT_MAX)) (PreH2 : ((snd ((Znth i sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((fst ((Znth i sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) prefix_2 0) >= INT_MIN)) (PreH5 : ((snd ((Znth i sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH6 : ((fst ((Znth i sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) prefix_2 0) > (snd ((Znth i sorted_2 __default__Prod_Z_Z))))) (PreH8 : (i <> 0)) (PreH9 : (na_pre = (Zlength (left)))) (PreH10 : (nb_pre = (Zlength (right)))) (PreH11 : (0 < na_pre)) (PreH12 : (na_pre <= 200000)) (PreH13 : (0 < nb_pre)) (PreH14 : (nb_pre <= 200000)) (PreH15 : (0 <= i)) (PreH16 : (i < nb_pre)) (PreH17 : ((Zlength (prefix_2)) = i)) (PreH18 : ((Zlength (sorted_2)) = nb_pre)) (PreH19 : (SegmentsBounded left )) (PreH20 : (Permutation right sorted_2 )) (PreH21 : (SegmentsBounded sorted_2 )) (PreH22 : (SegmentsSortedByLeft sorted_2 )) (PreH23 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (IntArray.full pref i prefix_2 )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted_2)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted_2)) )
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) prefix_2 0))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb_pre) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix (i + 1 ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref (i + 1 ) prefix )
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) (nb_pre - (i + 1 ) ) )
).

Definition overlap_entail_wit_3_2 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (i = 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < nb_pre)) (PreH10 : ((Zlength (prefix_2)) = i)) (PreH11 : ((Zlength (sorted_2)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted_2 )) (PreH14 : (SegmentsBounded sorted_2 )) (PreH15 : (SegmentsSortedByLeft sorted_2 )) (PreH16 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted_2)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted_2)) )
  **  (IntArray.full pref i prefix_2 )
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb_pre) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix (i + 1 ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref (i + 1 ) prefix )
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) (nb_pre - (i + 1 ) ) )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth i sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth i sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH4 : ((fst ((Znth i sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH5 : (i = 0)) (PreH6 : (na_pre = (Zlength (left)))) (PreH7 : (nb_pre = (Zlength (right)))) (PreH8 : (0 < na_pre)) (PreH9 : (na_pre <= 200000)) (PreH10 : (0 < nb_pre)) (PreH11 : (nb_pre <= 200000)) (PreH12 : (0 <= i)) (PreH13 : (i < nb_pre)) (PreH14 : ((Zlength (prefix_2)) = i)) (PreH15 : ((Zlength (sorted_2)) = nb_pre)) (PreH16 : (SegmentsBounded left )) (PreH17 : (Permutation right sorted_2 )) (PreH18 : (SegmentsBounded sorted_2 )) (PreH19 : (SegmentsSortedByLeft sorted_2 )) (PreH20 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted_2)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted_2)) )
  **  (IntArray.full pref i prefix_2 )
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb_pre) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix (i + 1 ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref (i + 1 ) prefix )
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) (nb_pre - (i + 1 ) ) )
).

Definition overlap_entail_wit_3_3 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix_2 0) <= (snd ((Znth i sorted_2 __default__Prod_Z_Z))))) (PreH2 : (i <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < nb_pre)) (PreH11 : ((Zlength (prefix_2)) = i)) (PreH12 : ((Zlength (sorted_2)) = nb_pre)) (PreH13 : (SegmentsBounded left )) (PreH14 : (Permutation right sorted_2 )) (PreH15 : (SegmentsBounded sorted_2 )) (PreH16 : (SegmentsSortedByLeft sorted_2 )) (PreH17 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (IntArray.full pref i prefix_2 )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted_2)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted_2)) )
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb_pre) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix (i + 1 ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref (i + 1 ) prefix )
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) (nb_pre - (i + 1 ) ) )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth i sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth i sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH4 : ((fst ((Znth i sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) prefix_2 0) <= (snd ((Znth i sorted_2 __default__Prod_Z_Z))))) (PreH6 : (i <> 0)) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 < na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 < nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (0 <= i)) (PreH14 : (i < nb_pre)) (PreH15 : ((Zlength (prefix_2)) = i)) (PreH16 : ((Zlength (sorted_2)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted_2 )) (PreH19 : (SegmentsBounded sorted_2 )) (PreH20 : (SegmentsSortedByLeft sorted_2 )) (PreH21 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (IntArray.full pref i prefix_2 )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted_2)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted_2)) )
  **  (((pref + (i * sizeof(INT)))) # Int  |-> (snd ((Znth i sorted_2 __default__Prod_Z_Z))))
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  EX (sorted: (@list (Z * Z)))  (prefix: (@list Z)) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb_pre) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix (i + 1 ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref (i + 1 ) prefix )
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) (nb_pre - (i + 1 ) ) )
).

Definition overlap_entail_wit_4 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= nb_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= nb_pre)) (PreH10 : ((Zlength (prefix_2)) = i)) (PreH11 : ((Zlength (sorted_2)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted_2 )) (PreH14 : (SegmentsBounded sorted_2 )) (PreH15 : (SegmentsSortedByLeft sorted_2 )) (PreH16 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.full pref i prefix_2 )
  **  (IntArray.undef_full (pref + (i * sizeof(INT))) (nb_pre - i ) )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= na_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right 0 0 ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (PreH1 : (i >= nb_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= nb_pre)) (PreH10 : ((Zlength (prefix_2)) = i)) (PreH11 : ((Zlength (sorted_2)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted_2 )) (PreH14 : (SegmentsBounded sorted_2 )) (PreH15 : (SegmentsSortedByLeft sorted_2 )) (PreH16 : (PrefixRightMaxima sorted_2 prefix_2 i )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.full pref i prefix_2 )
  **  (IntArray.undef_full (pref + (i * sizeof(INT))) (nb_pre - i ) )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= na_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right 0 0 ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
).

Definition overlap_entail_wit_5 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix_2: (@list Z)) (sorted_2: (@list (Z * Z))) (best: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted_2)) = nb_pre)) (PreH13 : ((Zlength (prefix_2)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted_2 )) (PreH16 : (SegmentsBounded sorted_2 )) (PreH17 : (SegmentsSortedByLeft sorted_2 )) (PreH18 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.full pref nb_pre prefix_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nb_pre) ” 
  &&  “ (nb_pre <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) 0 nb_pre ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (prefix_2: (@list Z)) (sorted_2: (@list (Z * Z))) (best: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted_2)) = nb_pre)) (PreH13 : ((Zlength (prefix_2)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted_2 )) (PreH16 : (SegmentsBounded sorted_2 )) (PreH17 : (SegmentsSortedByLeft sorted_2 )) (PreH18 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  TT && emp 
|--
  “ (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) 0 nb_pre ) ”
  &&  emp
).

Definition overlap_entail_wit_5_split_goal_1 := 
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (prefix_2: (@list Z)) (sorted_2: (@list (Z * Z))) (best: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (i < na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted_2)) = nb_pre)) (PreH13 : ((Zlength (prefix_2)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted_2 )) (PreH16 : (SegmentsBounded sorted_2 )) (PreH17 : (SegmentsSortedByLeft sorted_2 )) (PreH18 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) 0 nb_pre )
.

Definition overlap_entail_wit_6 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix_2: (@list Z)) (sorted_2: (@list (Z * Z))) (best: Z) (hi: Z) (lo: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (lo < hi)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted_2)) = nb_pre)) (PreH16 : ((Zlength (prefix_2)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted_2 )) (PreH19 : (SegmentsBounded sorted_2 )) (PreH20 : (SegmentsSortedByLeft sorted_2 )) (PreH21 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.full pref nb_pre prefix_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + hi ) ÷ 2 )) ” 
  &&  “ (((lo + hi ) ÷ 2 ) < hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi ) ”
  &&  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre ((lo + hi ) ÷ 2 ) (sublist (0) (((lo + hi ) ÷ 2 )) (sorted)) )
  **  ((&(((b_pre + (((lo + hi ) ÷ 2 ) * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth ((lo + hi ) ÷ 2 ) sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (((lo + hi ) ÷ 2 ) * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth ((lo + hi ) ÷ 2 ) sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((((lo + hi ) ÷ 2 ) + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - ((lo + hi ) ÷ 2 ) ) - 1 ) (sublist ((((lo + hi ) ÷ 2 ) + 1 )) (nb_pre) (sorted)) )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (prefix_2: (@list Z)) (sorted_2: (@list (Z * Z))) (best: Z) (hi: Z) (lo: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (lo < hi)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted_2)) = nb_pre)) (PreH16 : ((Zlength (prefix_2)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted_2 )) (PreH19 : (SegmentsBounded sorted_2 )) (PreH20 : (SegmentsSortedByLeft sorted_2 )) (PreH21 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + hi ) ÷ 2 )) ” 
  &&  “ (((lo + hi ) ÷ 2 ) < hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi ) ”
  &&  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre ((lo + hi ) ÷ 2 ) (sublist (0) (((lo + hi ) ÷ 2 )) (sorted)) )
  **  ((&(((b_pre + (((lo + hi ) ÷ 2 ) * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth ((lo + hi ) ÷ 2 ) sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (((lo + hi ) ÷ 2 ) * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth ((lo + hi ) ÷ 2 ) sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((((lo + hi ) ÷ 2 ) + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - ((lo + hi ) ÷ 2 ) ) - 1 ) (sublist ((((lo + hi ) ÷ 2 ) + 1 )) (nb_pre) (sorted)) )
).

Definition overlap_entail_wit_7_1 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (md: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) <= (fst ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= md)) (PreH12 : (md < hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted_2)) = nb_pre)) (PreH17 : ((Zlength (prefix_2)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted_2 )) (PreH20 : (SegmentsBounded sorted_2 )) (PreH21 : (SegmentsSortedByLeft sorted_2 )) (PreH22 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre md (sublist (0) (md) (sorted_2)) )
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((md + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - md ) - 1 ) (sublist ((md + 1 )) (nb_pre) (sorted_2)) )
  **  (IntArray.full pref nb_pre prefix_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= (md + 1 )) ” 
  &&  “ ((md + 1 ) <= hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) (md + 1 ) hi ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (md: Z) (hi: Z) (best: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth md sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH4 : ((fst ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH5 : ((snd ((Znth md sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH6 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH7 : ((snd ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH8 : ((fst ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH9 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) <= (fst ((Znth i left __default__Prod_Z_Z))))) (PreH10 : (na_pre = (Zlength (left)))) (PreH11 : (nb_pre = (Zlength (right)))) (PreH12 : (0 < na_pre)) (PreH13 : (na_pre <= 200000)) (PreH14 : (0 < nb_pre)) (PreH15 : (nb_pre <= 200000)) (PreH16 : (0 <= i)) (PreH17 : (i < na_pre)) (PreH18 : (0 <= lo)) (PreH19 : (lo <= md)) (PreH20 : (md < hi)) (PreH21 : (hi <= nb_pre)) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : ((Zlength (sorted_2)) = nb_pre)) (PreH25 : ((Zlength (prefix_2)) = nb_pre)) (PreH26 : (SegmentsBounded left )) (PreH27 : (Permutation right sorted_2 )) (PreH28 : (SegmentsBounded sorted_2 )) (PreH29 : (SegmentsSortedByLeft sorted_2 )) (PreH30 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH31 : (DirectedOverlapMaximumPrefix left right i best )) (PreH32 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre md (sublist (0) (md) (sorted_2)) )
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((md + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - md ) - 1 ) (sublist ((md + 1 )) (nb_pre) (sorted_2)) )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= (md + 1 )) ” 
  &&  “ ((md + 1 ) <= hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) (md + 1 ) hi ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_entail_wit_7_2 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (md: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) > (fst ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= md)) (PreH12 : (md < hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted_2)) = nb_pre)) (PreH17 : ((Zlength (prefix_2)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted_2 )) (PreH20 : (SegmentsBounded sorted_2 )) (PreH21 : (SegmentsSortedByLeft sorted_2 )) (PreH22 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre md (sublist (0) (md) (sorted_2)) )
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((md + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - md ) - 1 ) (sublist ((md + 1 )) (nb_pre) (sorted_2)) )
  **  (IntArray.full pref nb_pre prefix_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= md) ” 
  &&  “ (md <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo md ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (md: Z) (hi: Z) (best: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth md sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH4 : ((fst ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH5 : ((snd ((Znth md sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH6 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) >= INT_MIN)) (PreH7 : ((snd ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH8 : ((fst ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH9 : ((fst ((Znth md sorted_2 __default__Prod_Z_Z))) > (fst ((Znth i left __default__Prod_Z_Z))))) (PreH10 : (na_pre = (Zlength (left)))) (PreH11 : (nb_pre = (Zlength (right)))) (PreH12 : (0 < na_pre)) (PreH13 : (na_pre <= 200000)) (PreH14 : (0 < nb_pre)) (PreH15 : (nb_pre <= 200000)) (PreH16 : (0 <= i)) (PreH17 : (i < na_pre)) (PreH18 : (0 <= lo)) (PreH19 : (lo <= md)) (PreH20 : (md < hi)) (PreH21 : (hi <= nb_pre)) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : ((Zlength (sorted_2)) = nb_pre)) (PreH25 : ((Zlength (prefix_2)) = nb_pre)) (PreH26 : (SegmentsBounded left )) (PreH27 : (Permutation right sorted_2 )) (PreH28 : (SegmentsBounded sorted_2 )) (PreH29 : (SegmentsSortedByLeft sorted_2 )) (PreH30 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH31 : (DirectedOverlapMaximumPrefix left right i best )) (PreH32 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre md (sublist (0) (md) (sorted_2)) )
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  ((&(((b_pre + (md * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth md sorted_2 __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((md + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - md ) - 1 ) (sublist ((md + 1 )) (nb_pre) (sorted_2)) )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= md) ” 
  &&  “ (md <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo md ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_entail_wit_8 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix_2: (@list Z)) (sorted_2: (@list (Z * Z))) (best: Z) (hi: Z) (lo: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (lo >= hi)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted_2)) = nb_pre)) (PreH16 : ((Zlength (prefix_2)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted_2 )) (PreH19 : (SegmentsBounded sorted_2 )) (PreH20 : (SegmentsSortedByLeft sorted_2 )) (PreH21 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.full pref nb_pre prefix_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo = hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi ) ”
  &&  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (prefix_2: (@list Z)) (sorted_2: (@list (Z * Z))) (best: Z) (hi: Z) (lo: Z) (i: Z)  __default__Prod_Z_Z (PreH1 : (lo >= hi)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted_2)) = nb_pre)) (PreH16 : ((Zlength (prefix_2)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted_2 )) (PreH19 : (SegmentsBounded sorted_2 )) (PreH20 : (SegmentsSortedByLeft sorted_2 )) (PreH21 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo = hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi ) ”
  &&  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_entail_wit_9_1 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) > best)) (PreH2 : ((Znth (lo - 1 ) prefix_2 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted_2)) = nb_pre)) (PreH17 : ((Zlength (prefix_2)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted_2 )) (PreH20 : (SegmentsBounded sorted_2 )) (PreH21 : (SegmentsSortedByLeft sorted_2 )) (PreH22 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix_2 )
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= ((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) )) ” 
  &&  “ (((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) ((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH4 : ((fst ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH5 : (((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) > best)) (PreH6 : ((Znth (lo - 1 ) prefix_2 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 < na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 < nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (0 <= i)) (PreH14 : (i < na_pre)) (PreH15 : (0 <= lo)) (PreH16 : (lo = hi)) (PreH17 : (hi <= nb_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000000)) (PreH20 : ((Zlength (sorted_2)) = nb_pre)) (PreH21 : ((Zlength (prefix_2)) = nb_pre)) (PreH22 : (SegmentsBounded left )) (PreH23 : (Permutation right sorted_2 )) (PreH24 : (SegmentsBounded sorted_2 )) (PreH25 : (SegmentsSortedByLeft sorted_2 )) (PreH26 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH27 : (DirectedOverlapMaximumPrefix left right i best )) (PreH28 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH29 : (lo <> 0)) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= ((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) )) ” 
  &&  “ (((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) ((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_entail_wit_9_2 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) > best)) (PreH2 : ((Znth (lo - 1 ) prefix_2 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted_2)) = nb_pre)) (PreH17 : ((Zlength (prefix_2)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted_2 )) (PreH20 : (SegmentsBounded sorted_2 )) (PreH21 : (SegmentsSortedByLeft sorted_2 )) (PreH22 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix_2 )
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) )) ” 
  &&  “ (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH4 : ((fst ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH5 : (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) > best)) (PreH6 : ((Znth (lo - 1 ) prefix_2 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 < na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 < nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (0 <= i)) (PreH14 : (i < na_pre)) (PreH15 : (0 <= lo)) (PreH16 : (lo = hi)) (PreH17 : (hi <= nb_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000000)) (PreH20 : ((Zlength (sorted_2)) = nb_pre)) (PreH21 : ((Zlength (prefix_2)) = nb_pre)) (PreH22 : (SegmentsBounded left )) (PreH23 : (Permutation right sorted_2 )) (PreH24 : (SegmentsBounded sorted_2 )) (PreH25 : (SegmentsSortedByLeft sorted_2 )) (PreH26 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH27 : (DirectedOverlapMaximumPrefix left right i best )) (PreH28 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH29 : (lo <> 0)) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) )) ” 
  &&  “ (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) ((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_entail_wit_9_3 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= best)) (PreH2 : ((Znth (lo - 1 ) prefix_2 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted_2)) = nb_pre)) (PreH17 : ((Zlength (prefix_2)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted_2 )) (PreH20 : (SegmentsBounded sorted_2 )) (PreH21 : (SegmentsSortedByLeft sorted_2 )) (PreH22 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix_2 )
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) best ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH4 : ((fst ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH5 : (((Znth (lo - 1 ) prefix_2 0) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= best)) (PreH6 : ((Znth (lo - 1 ) prefix_2 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 < na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 < nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (0 <= i)) (PreH14 : (i < na_pre)) (PreH15 : (0 <= lo)) (PreH16 : (lo = hi)) (PreH17 : (hi <= nb_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000000)) (PreH20 : ((Zlength (sorted_2)) = nb_pre)) (PreH21 : ((Zlength (prefix_2)) = nb_pre)) (PreH22 : (SegmentsBounded left )) (PreH23 : (Permutation right sorted_2 )) (PreH24 : (SegmentsBounded sorted_2 )) (PreH25 : (SegmentsSortedByLeft sorted_2 )) (PreH26 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH27 : (DirectedOverlapMaximumPrefix left right i best )) (PreH28 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH29 : (lo <> 0)) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) best ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_entail_wit_9_4 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= best)) (PreH2 : ((Znth (lo - 1 ) prefix_2 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < na_pre)) (PreH11 : (0 <= lo)) (PreH12 : (lo = hi)) (PreH13 : (hi <= nb_pre)) (PreH14 : (0 <= best)) (PreH15 : (best <= 1000000000)) (PreH16 : ((Zlength (sorted_2)) = nb_pre)) (PreH17 : ((Zlength (prefix_2)) = nb_pre)) (PreH18 : (SegmentsBounded left )) (PreH19 : (Permutation right sorted_2 )) (PreH20 : (SegmentsBounded sorted_2 )) (PreH21 : (SegmentsSortedByLeft sorted_2 )) (PreH22 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH23 : (DirectedOverlapMaximumPrefix left right i best )) (PreH24 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH25 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix_2 )
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) best ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH4 : ((fst ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH5 : (((snd ((Znth i left __default__Prod_Z_Z))) - (fst ((Znth i left __default__Prod_Z_Z))) ) <= best)) (PreH6 : ((Znth (lo - 1 ) prefix_2 0) >= (snd ((Znth i left __default__Prod_Z_Z))))) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 < na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 < nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (0 <= i)) (PreH14 : (i < na_pre)) (PreH15 : (0 <= lo)) (PreH16 : (lo = hi)) (PreH17 : (hi <= nb_pre)) (PreH18 : (0 <= best)) (PreH19 : (best <= 1000000000)) (PreH20 : ((Zlength (sorted_2)) = nb_pre)) (PreH21 : ((Zlength (prefix_2)) = nb_pre)) (PreH22 : (SegmentsBounded left )) (PreH23 : (Permutation right sorted_2 )) (PreH24 : (SegmentsBounded sorted_2 )) (PreH25 : (SegmentsSortedByLeft sorted_2 )) (PreH26 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH27 : (DirectedOverlapMaximumPrefix left right i best )) (PreH28 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH29 : (lo <> 0)) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) best ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_entail_wit_9_5 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (na_pre = (Zlength (left)))) (PreH2 : (nb_pre = (Zlength (right)))) (PreH3 : (0 < na_pre)) (PreH4 : (na_pre <= 200000)) (PreH5 : (0 < nb_pre)) (PreH6 : (nb_pre <= 200000)) (PreH7 : (0 <= i)) (PreH8 : (i < na_pre)) (PreH9 : (0 <= lo)) (PreH10 : (lo = hi)) (PreH11 : (hi <= nb_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= 1000000000)) (PreH14 : ((Zlength (sorted_2)) = nb_pre)) (PreH15 : ((Zlength (prefix_2)) = nb_pre)) (PreH16 : (SegmentsBounded left )) (PreH17 : (Permutation right sorted_2 )) (PreH18 : (SegmentsBounded sorted_2 )) (PreH19 : (SegmentsSortedByLeft sorted_2 )) (PreH20 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH21 : (DirectedOverlapMaximumPrefix left right i best )) (PreH22 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH23 : (lo = 0)) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
  **  (IntArray.full pref nb_pre prefix_2 )
|--
  EX (prefix: (@list Z))  (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) best ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted_2: (@list (Z * Z))) (prefix_2: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z)  __default__Prod_Z_Z (PreH1 : ((snd ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH2 : ((fst ((Znth i left __default__Prod_Z_Z))) <= INT_MAX)) (PreH3 : ((snd ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH4 : ((fst ((Znth i left __default__Prod_Z_Z))) >= INT_MIN)) (PreH5 : (na_pre = (Zlength (left)))) (PreH6 : (nb_pre = (Zlength (right)))) (PreH7 : (0 < na_pre)) (PreH8 : (na_pre <= 200000)) (PreH9 : (0 < nb_pre)) (PreH10 : (nb_pre <= 200000)) (PreH11 : (0 <= i)) (PreH12 : (i < na_pre)) (PreH13 : (0 <= lo)) (PreH14 : (lo = hi)) (PreH15 : (hi <= nb_pre)) (PreH16 : (0 <= best)) (PreH17 : (best <= 1000000000)) (PreH18 : ((Zlength (sorted_2)) = nb_pre)) (PreH19 : ((Zlength (prefix_2)) = nb_pre)) (PreH20 : (SegmentsBounded left )) (PreH21 : (Permutation right sorted_2 )) (PreH22 : (SegmentsBounded sorted_2 )) (PreH23 : (SegmentsSortedByLeft sorted_2 )) (PreH24 : (PrefixRightMaxima sorted_2 prefix_2 nb_pre )) (PreH25 : (DirectedOverlapMaximumPrefix left right i best )) (PreH26 : (UpperBoundBracket sorted_2 (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH27 : (lo = 0)) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted_2 )
|--
  EX (sorted: (@list (Z * Z))) ,
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix_2)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix_2 nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right (i + 1 ) best ) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
).

Definition overlap_return_wit_1 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (i: Z) (PreH1 : (i >= na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : ((Zlength (prefix)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted )) (PreH16 : (SegmentsBounded sorted )) (PreH17 : (SegmentsSortedByLeft sorted )) (PreH18 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
|--
  EX (right_after: (@list (Z * Z))) ,
  “ ((Zlength (right_after)) = nb_pre) ” 
  &&  “ (Permutation right right_after ) ” 
  &&  “ (SegmentsBounded right_after ) ” 
  &&  “ (DirectedOverlapMaximum left right best ) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right_after )
) \/
(
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (i: Z) (PreH1 : (i >= na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : ((Zlength (prefix)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted )) (PreH16 : (SegmentsBounded sorted )) (PreH17 : (SegmentsSortedByLeft sorted )) (PreH18 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  TT && emp 
|--
  “ (DirectedOverlapMaximum left right best ) ”
  &&  emp
).

Definition overlap_return_wit_1_split_goal_1 := 
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (i: Z) (PreH1 : (i >= na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : ((Zlength (prefix)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted )) (PreH16 : (SegmentsBounded sorted )) (PreH17 : (SegmentsSortedByLeft sorted )) (PreH18 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  (DirectedOverlapMaximum left right best )
.

Definition overlap_return_wit_2 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (na_pre = 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 <= na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 <= nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (SegmentsBounded left )) (PreH9 : (SegmentsBounded right )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  EX (right_after: (@list (Z * Z))) ,
  “ ((Zlength (right_after)) = nb_pre) ” 
  &&  “ (Permutation right right_after ) ” 
  &&  “ (SegmentsBounded right_after ) ” 
  &&  “ (DirectedOverlapMaximum left right 0 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right_after )
) \/
(
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (na_pre = 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 <= na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 <= nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (SegmentsBounded left )) (PreH9 : (SegmentsBounded right )) ,
  TT && emp 
|--
  “ (DirectedOverlapMaximum left right 0 ) ” 
  &&  “ (Permutation right right ) ”
  &&  emp
).

Definition overlap_return_wit_2_split_goal_1 := 
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (na_pre = 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 <= na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 <= nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (SegmentsBounded left )) (PreH9 : (SegmentsBounded right )) ,
  (DirectedOverlapMaximum left right 0 )
.

Definition overlap_return_wit_2_split_goal_2 := 
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (na_pre = 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 <= na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 <= nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (SegmentsBounded left )) (PreH9 : (SegmentsBounded right )) ,
  (Permutation right right )
.

Definition overlap_return_wit_3 := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre = 0)) (PreH2 : (na_pre <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 <= na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 <= nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (SegmentsBounded left )) (PreH10 : (SegmentsBounded right )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  EX (right_after: (@list (Z * Z))) ,
  “ ((Zlength (right_after)) = nb_pre) ” 
  &&  “ (Permutation right right_after ) ” 
  &&  “ (SegmentsBounded right_after ) ” 
  &&  “ (DirectedOverlapMaximum left right 0 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ”
  &&  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right_after )
) \/
(
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre = 0)) (PreH2 : (na_pre <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 <= na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 <= nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (SegmentsBounded left )) (PreH10 : (SegmentsBounded right )) ,
  TT && emp 
|--
  “ (DirectedOverlapMaximum left right 0 ) ” 
  &&  “ (Permutation right right ) ”
  &&  emp
).

Definition overlap_return_wit_3_split_goal_1 := 
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre = 0)) (PreH2 : (na_pre <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 <= na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 <= nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (SegmentsBounded left )) (PreH10 : (SegmentsBounded right )) ,
  (DirectedOverlapMaximum left right 0 )
.

Definition overlap_return_wit_3_split_goal_2 := 
forall (nb_pre: Z) (na_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre = 0)) (PreH2 : (na_pre <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 <= na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 <= nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (SegmentsBounded left )) (PreH10 : (SegmentsBounded right )) ,
  (Permutation right right )
.

Definition overlap_partial_solve_wit_1_pure := 
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre <> 0)) (PreH2 : (na_pre <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 <= na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 <= nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (SegmentsBounded left )) (PreH10 : (SegmentsBounded right )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (SegmentsBounded right ) ” 
  &&  “ (SegmentAllocationSize sizeof( "<anonymous struct>" ) 1 ) ”
) \/
(
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre <= INT_MAX)) (PreH2 : (na_pre <= INT_MAX)) (PreH3 : (nb_pre >= INT_MIN)) (PreH4 : (na_pre >= INT_MIN)) (PreH5 : (nb_pre <> 0)) (PreH6 : (na_pre <> 0)) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 <= na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 <= nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (SegmentsBounded left )) (PreH14 : (SegmentsBounded right )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  “ (SegmentAllocationSize sizeof( "<anonymous struct>" ) 1 ) ”
).

Definition overlap_partial_solve_wit_1_pure_split_goal_1 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre <= INT_MAX)) (PreH2 : (na_pre <= INT_MAX)) (PreH3 : (nb_pre >= INT_MIN)) (PreH4 : (na_pre >= INT_MIN)) (PreH5 : (nb_pre <> 0)) (PreH6 : (na_pre <> 0)) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 <= na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 <= nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (SegmentsBounded left )) (PreH14 : (SegmentsBounded right )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  “ (SegmentAllocationSize sizeof( "<anonymous struct>" ) 1 ) ”
.

Definition overlap_partial_solve_wit_1_aux := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (PreH1 : (nb_pre <> 0)) (PreH2 : (na_pre <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 <= na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 <= nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (SegmentsBounded left )) (PreH10 : (SegmentsBounded right )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre right )
|--
  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (SegmentsBounded right ) ” 
  &&  “ (SegmentAllocationSize sizeof( "<anonymous struct>" ) 1 ) ” 
  &&  “ (nb_pre <> 0) ” 
  &&  “ (na_pre <> 0) ” 
  &&  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 <= na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 <= nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (SegmentsBounded right ) ”
  &&  (SegArray.full b_pre nb_pre right )
  **  (SegArray.full a_pre na_pre left )
.

Definition overlap_partial_solve_wit_1 := overlap_partial_solve_wit_1_pure -> overlap_partial_solve_wit_1_aux.

Definition overlap_partial_solve_wit_2_pure := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (PreH1 : ((Zlength (sorted)) = nb_pre)) (PreH2 : (Permutation right sorted )) (PreH3 : (SegmentsBounded sorted )) (PreH4 : (SegmentsSortedByLeft sorted )) (PreH5 : (nb_pre <> 0)) (PreH6 : (na_pre <> 0)) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 <= na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 <= nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (SegmentsBounded left )) (PreH14 : (SegmentsBounded right )) ,
  ((( &( "pref" ) )) # Ptr  |->_)
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  (SegArray.full a_pre na_pre left )
|--
  “ (0 <= nb_pre) ” 
  &&  “ ((nb_pre * sizeof(INT) ) = (nb_pre * sizeof(INT) )) ”
.

Definition overlap_partial_solve_wit_2_aux := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (PreH1 : ((Zlength (sorted)) = nb_pre)) (PreH2 : (Permutation right sorted )) (PreH3 : (SegmentsBounded sorted )) (PreH4 : (SegmentsSortedByLeft sorted )) (PreH5 : (nb_pre <> 0)) (PreH6 : (na_pre <> 0)) (PreH7 : (na_pre = (Zlength (left)))) (PreH8 : (nb_pre = (Zlength (right)))) (PreH9 : (0 <= na_pre)) (PreH10 : (na_pre <= 200000)) (PreH11 : (0 <= nb_pre)) (PreH12 : (nb_pre <= 200000)) (PreH13 : (SegmentsBounded left )) (PreH14 : (SegmentsBounded right )) ,
  (SegArray.full b_pre nb_pre sorted )
  **  (SegArray.full a_pre na_pre left )
|--
  “ (0 <= nb_pre) ” 
  &&  “ ((nb_pre * sizeof(INT) ) = (nb_pre * sizeof(INT) )) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (nb_pre <> 0) ” 
  &&  “ (na_pre <> 0) ” 
  &&  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 <= na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 <= nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (SegmentsBounded right ) ”
  &&  (SegArray.full b_pre nb_pre sorted )
  **  (SegArray.full a_pre na_pre left )
.

Definition overlap_partial_solve_wit_2 := overlap_partial_solve_wit_2_pure -> overlap_partial_solve_wit_2_aux.

Definition overlap_partial_solve_wit_3 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (i <> 0)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < nb_pre)) (PreH10 : ((Zlength (prefix)) = i)) (PreH11 : ((Zlength (sorted)) = nb_pre)) (PreH12 : (SegmentsBounded left )) (PreH13 : (Permutation right sorted )) (PreH14 : (SegmentsBounded sorted )) (PreH15 : (SegmentsSortedByLeft sorted )) (PreH16 : (PrefixRightMaxima sorted prefix i )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  (IntArray.full pref i prefix )
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ (i <> 0) ” 
  &&  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nb_pre) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix i ) ”
  &&  (((pref + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) prefix 0))
  **  (IntArray.missing_i pref (i - 1 ) 0 i prefix )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
.

Definition overlap_partial_solve_wit_4 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (i - 1 ) prefix 0) > (snd ((Znth i sorted __default__Prod_Z_Z))))) (PreH2 : (i <> 0)) (PreH3 : (na_pre = (Zlength (left)))) (PreH4 : (nb_pre = (Zlength (right)))) (PreH5 : (0 < na_pre)) (PreH6 : (na_pre <= 200000)) (PreH7 : (0 < nb_pre)) (PreH8 : (nb_pre <= 200000)) (PreH9 : (0 <= i)) (PreH10 : (i < nb_pre)) (PreH11 : ((Zlength (prefix)) = i)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : (SegmentsBounded left )) (PreH14 : (Permutation right sorted )) (PreH15 : (SegmentsBounded sorted )) (PreH16 : (SegmentsSortedByLeft sorted )) (PreH17 : (PrefixRightMaxima sorted prefix i )) ,
  (IntArray.full pref i prefix )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
|--
  “ ((Znth (i - 1 ) prefix 0) > (snd ((Znth i sorted __default__Prod_Z_Z)))) ” 
  &&  “ (i <> 0) ” 
  &&  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < nb_pre) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix i ) ”
  &&  (((pref + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) prefix 0))
  **  (IntArray.missing_i pref (i - 1 ) 0 i prefix )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre i (sublist (0) (i) (sorted)) )
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i sorted __default__Prod_Z_Z))))
  **  ((&(((b_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i sorted __default__Prod_Z_Z))))
  **  (SegArray.full (b_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((nb_pre - i ) - 1 ) (sublist ((i + 1 )) (nb_pre) (sorted)) )
  **  (((pref + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_full (pref + ((i + 1 ) * sizeof(INT))) ((nb_pre - i ) - 1 ) )
.

Definition overlap_partial_solve_wit_5 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : (na_pre = (Zlength (left)))) (PreH2 : (nb_pre = (Zlength (right)))) (PreH3 : (0 < na_pre)) (PreH4 : (na_pre <= 200000)) (PreH5 : (0 < nb_pre)) (PreH6 : (nb_pre <= 200000)) (PreH7 : (0 <= i)) (PreH8 : (i < na_pre)) (PreH9 : (0 <= lo)) (PreH10 : (lo = hi)) (PreH11 : (hi <= nb_pre)) (PreH12 : (0 <= best)) (PreH13 : (best <= 1000000000)) (PreH14 : ((Zlength (sorted)) = nb_pre)) (PreH15 : ((Zlength (prefix)) = nb_pre)) (PreH16 : (SegmentsBounded left )) (PreH17 : (Permutation right sorted )) (PreH18 : (SegmentsBounded sorted )) (PreH19 : (SegmentsSortedByLeft sorted )) (PreH20 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH21 : (DirectedOverlapMaximumPrefix left right i best )) (PreH22 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH23 : (lo <> 0)) ,
  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
|--
  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo = hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi ) ” 
  &&  “ (lo <> 0) ”
  &&  (((pref + ((lo - 1 ) * sizeof(INT)))) # Int  |-> (Znth (lo - 1 ) prefix 0))
  **  (IntArray.missing_i pref (lo - 1 ) 0 nb_pre prefix )
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
.

Definition overlap_partial_solve_wit_6 := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (sorted: (@list (Z * Z))) (prefix: (@list Z)) (i: Z) (lo: Z) (hi: Z) (best: Z) (pref: Z)  __default__Prod_Z_Z (PreH1 : ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z))))) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i < na_pre)) (PreH10 : (0 <= lo)) (PreH11 : (lo = hi)) (PreH12 : (hi <= nb_pre)) (PreH13 : (0 <= best)) (PreH14 : (best <= 1000000000)) (PreH15 : ((Zlength (sorted)) = nb_pre)) (PreH16 : ((Zlength (prefix)) = nb_pre)) (PreH17 : (SegmentsBounded left )) (PreH18 : (Permutation right sorted )) (PreH19 : (SegmentsBounded sorted )) (PreH20 : (SegmentsSortedByLeft sorted )) (PreH21 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH22 : (DirectedOverlapMaximumPrefix left right i best )) (PreH23 : (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi )) (PreH24 : (lo <> 0)) ,
  (IntArray.full pref nb_pre prefix )
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
|--
  “ ((Znth (lo - 1 ) prefix 0) < (snd ((Znth i left __default__Prod_Z_Z)))) ” 
  &&  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < na_pre) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo = hi) ” 
  &&  “ (hi <= nb_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ” 
  &&  “ (UpperBoundBracket sorted (fst ((Znth i left __default__Prod_Z_Z))) lo hi ) ” 
  &&  “ (lo <> 0) ”
  &&  (((pref + ((lo - 1 ) * sizeof(INT)))) # Int  |-> (Znth (lo - 1 ) prefix 0))
  **  (IntArray.missing_i pref (lo - 1 ) 0 nb_pre prefix )
  **  (SegArray.full a_pre i (sublist (0) (i) (left)) )
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (fst ((Znth i left __default__Prod_Z_Z))))
  **  ((&(((a_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (snd ((Znth i left __default__Prod_Z_Z))))
  **  (SegArray.full (a_pre + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((na_pre - i ) - 1 ) (sublist ((i + 1 )) (na_pre) (left)) )
  **  (SegArray.full b_pre nb_pre sorted )
.

Definition overlap_partial_solve_wit_7_pure := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (i: Z) (PreH1 : (i >= na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : ((Zlength (prefix)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted )) (PreH16 : (SegmentsBounded sorted )) (PreH17 : (SegmentsSortedByLeft sorted )) (PreH18 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "na" ) )) # Int  |-> na_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nb" ) )) # Int  |-> nb_pre)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  ((( &( "pref" ) )) # Ptr  |-> pref)
  **  (IntArray.full pref nb_pre prefix )
|--
  “ ((Zlength (prefix)) = nb_pre) ”
.

Definition overlap_partial_solve_wit_7_aux := 
forall (nb_pre: Z) (b_pre: Z) (na_pre: Z) (a_pre: Z) (right: (@list (Z * Z))) (left: (@list (Z * Z))) (pref: Z) (prefix: (@list Z)) (sorted: (@list (Z * Z))) (best: Z) (i: Z) (PreH1 : (i >= na_pre)) (PreH2 : (na_pre = (Zlength (left)))) (PreH3 : (nb_pre = (Zlength (right)))) (PreH4 : (0 < na_pre)) (PreH5 : (na_pre <= 200000)) (PreH6 : (0 < nb_pre)) (PreH7 : (nb_pre <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= na_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 1000000000)) (PreH12 : ((Zlength (sorted)) = nb_pre)) (PreH13 : ((Zlength (prefix)) = nb_pre)) (PreH14 : (SegmentsBounded left )) (PreH15 : (Permutation right sorted )) (PreH16 : (SegmentsBounded sorted )) (PreH17 : (SegmentsSortedByLeft sorted )) (PreH18 : (PrefixRightMaxima sorted prefix nb_pre )) (PreH19 : (DirectedOverlapMaximumPrefix left right i best )) ,
  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
  **  (IntArray.full pref nb_pre prefix )
|--
  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (i >= na_pre) ” 
  &&  “ (na_pre = (Zlength (left))) ” 
  &&  “ (nb_pre = (Zlength (right))) ” 
  &&  “ (0 < na_pre) ” 
  &&  “ (na_pre <= 200000) ” 
  &&  “ (0 < nb_pre) ” 
  &&  “ (nb_pre <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ ((Zlength (sorted)) = nb_pre) ” 
  &&  “ ((Zlength (prefix)) = nb_pre) ” 
  &&  “ (SegmentsBounded left ) ” 
  &&  “ (Permutation right sorted ) ” 
  &&  “ (SegmentsBounded sorted ) ” 
  &&  “ (SegmentsSortedByLeft sorted ) ” 
  &&  “ (PrefixRightMaxima sorted prefix nb_pre ) ” 
  &&  “ (DirectedOverlapMaximumPrefix left right i best ) ”
  &&  (IntArray.full pref nb_pre prefix )
  **  (SegArray.full a_pre na_pre left )
  **  (SegArray.full b_pre nb_pre sorted )
.

Definition overlap_partial_solve_wit_7 := overlap_partial_solve_wit_7_pure -> overlap_partial_solve_wit_7_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((( &( "ny" ) )) # Int  |->_)
  **  ((( &( "nx" ) )) # Int  |-> 0)
  **  (SegArray.undef_full retval_2 n_pre )
  **  ((( &( "y" ) )) # Ptr  |-> retval_2)
  **  (SegArray.undef_full retval n_pre )
  **  ((( &( "x" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((( &( "nx" ) )) # Int  |->_)
  **  (SegArray.undef_full retval_2 n_pre )
  **  ((( &( "y" ) )) # Ptr  |-> retval_2)
  **  (SegArray.undef_full retval n_pre )
  **  ((( &( "x" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((( &( "base" ) )) # Int64  |->_)
  **  ((( &( "ny" ) )) # Int  |-> 0)
  **  ((( &( "nx" ) )) # Int  |-> 0)
  **  (SegArray.undef_full retval_2 n_pre )
  **  ((( &( "y" ) )) # Ptr  |-> retval_2)
  **  (SegArray.undef_full retval n_pre )
  **  ((( &( "x" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "base" ) )) # Int64  |-> 0)
  **  ((( &( "ny" ) )) # Int  |-> 0)
  **  ((( &( "nx" ) )) # Int  |-> 0)
  **  (SegArray.undef_full retval_2 n_pre )
  **  ((( &( "y" ) )) # Ptr  |-> retval_2)
  **  (SegArray.undef_full retval n_pre )
  **  ((( &( "x" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (((Znth i values 0) - (Znth i b_data 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i values 0) - (Znth i b_data 0) )) ”
.

Definition solver_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "d" ) )) # Int  |-> ((Znth i values 0) - (Znth i b_data 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d < 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ ((base - d ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (base - d )) ”
.

Definition solver_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d < 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> (base - d ))
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i values 0))
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i b_data 0))
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ ((nx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nx + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) >= 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (b_data)) = (Zlength (values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= nx)) (PreH12 : (nx <= i)) (PreH13 : (0 <= ny)) (PreH14 : (ny <= i)) (PreH15 : ((Zlength (increasing)) = nx)) (PreH16 : ((Zlength (decreasing)) = ny)) (PreH17 : (0 <= base)) (PreH18 : (base <= (999999999 * i ))) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "d" ) )) # Int  |-> ((Znth i values 0) - (Znth i b_data 0) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d > 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
|--
  “ ((base + d ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (base + d )) ”
.

Definition solver_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d > 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> (base + d ))
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i b_data 0))
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i values 0))
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
|--
  “ ((ny + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ny + 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d < 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> (nx + 1 ))
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> (base - d ))
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i values 0))
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i b_data 0))
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d > 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> (ny + 1 ))
  **  ((( &( "base" ) )) # Int64  |-> (base + d ))
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i b_data 0))
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i values 0))
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) <= 0)) (PreH2 : (((Znth i values 0) - (Znth i b_data 0) ) >= 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= nx)) (PreH13 : (nx <= i)) (PreH14 : (0 <= ny)) (PreH15 : (ny <= i)) (PreH16 : ((Zlength (increasing)) = nx)) (PreH17 : ((Zlength (decreasing)) = ny)) (PreH18 : (0 <= base)) (PreH19 : (base <= (999999999 * i ))) (PreH20 : (SolverScanState values b_data i base increasing decreasing )) (PreH21 : (SegmentsBounded increasing )) (PreH22 : (SegmentsBounded decreasing )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  “ ((base - (2 * best ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (base - (2 * best ) )) ”
.

Definition solver_safety_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  “ ((2 * best ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (2 * best )) ”
.

Definition solver_safety_wit_17 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  “ (2 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 2) ”
.

Definition solver_entail_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  (SegArray.undef_full retval_2 n_pre )
  **  (SegArray.undef_full retval n_pre )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (increasing)) = 0) ” 
  &&  “ ((Zlength (decreasing)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (999999999 * 0 )) ” 
  &&  “ (SolverScanState values b_data 0 0 increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full retval 0 increasing )
  **  (SegArray.undef_full (retval + (0 * sizeof( "<anonymous struct>" ))) (n_pre - 0 ) )
  **  (SegArray.full retval_2 0 decreasing )
  **  (SegArray.undef_full (retval_2 + (0 * sizeof( "<anonymous struct>" ))) (n_pre - 0 ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  (SegArray.undef_full retval_2 n_pre )
  **  (SegArray.undef_full retval n_pre )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (increasing)) = 0) ” 
  &&  “ ((Zlength (decreasing)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (999999999 * 0 )) ” 
  &&  “ (SolverScanState values b_data 0 0 increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (SegArray.full retval 0 increasing )
  **  (SegArray.undef_full (retval + (0 * sizeof( "<anonymous struct>" ))) (n_pre - 0 ) )
  **  (SegArray.full retval_2 0 decreasing )
  **  (SegArray.undef_full (retval_2 + (0 * sizeof( "<anonymous struct>" ))) (n_pre - 0 ) )
).

Definition solver_entail_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing_2: (@list (Z * Z))) (increasing_2: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) < 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (b_data)) = (Zlength (values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= nx)) (PreH12 : (nx <= i)) (PreH13 : (0 <= ny)) (PreH14 : (ny <= i)) (PreH15 : ((Zlength (increasing_2)) = nx)) (PreH16 : ((Zlength (decreasing_2)) = ny)) (PreH17 : (0 <= base)) (PreH18 : (base <= (999999999 * i ))) (PreH19 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH20 : (SegmentsBounded increasing_2 )) (PreH21 : (SegmentsBounded decreasing_2 )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing_2 )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_2 )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (((Znth i values 0) - (Znth i b_data 0) ) = ((Znth i values 0) - (Znth i b_data 0) )) ” 
  &&  “ (((Znth i values 0) - (Znth i b_data 0) ) < 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing_2: (@list (Z * Z))) (increasing_2: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) < 0)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : ((Zlength (b_data)) = (Zlength (values)))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= nx)) (PreH12 : (nx <= i)) (PreH13 : (0 <= ny)) (PreH14 : (ny <= i)) (PreH15 : ((Zlength (increasing_2)) = nx)) (PreH16 : ((Zlength (decreasing_2)) = ny)) (PreH17 : (0 <= base)) (PreH18 : (base <= (999999999 * i ))) (PreH19 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH20 : (SegmentsBounded increasing_2 )) (PreH21 : (SegmentsBounded decreasing_2 )) ,
  (SegArray.full x nx increasing_2 )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_2 )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (x_3: Z)  (x_2: Z)  (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (((Znth i values 0) - (Znth i b_data 0) ) < 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> x_3)
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> x_2)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
).

Definition solver_entail_wit_3 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing_2: (@list (Z * Z))) (increasing_2: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) > 0)) (PreH2 : (((Znth i values 0) - (Znth i b_data 0) ) >= 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= nx)) (PreH13 : (nx <= i)) (PreH14 : (0 <= ny)) (PreH15 : (ny <= i)) (PreH16 : ((Zlength (increasing_2)) = nx)) (PreH17 : ((Zlength (decreasing_2)) = ny)) (PreH18 : (0 <= base)) (PreH19 : (base <= (999999999 * i ))) (PreH20 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH21 : (SegmentsBounded increasing_2 )) (PreH22 : (SegmentsBounded decreasing_2 )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing_2 )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_2 )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (((Znth i values 0) - (Znth i b_data 0) ) = ((Znth i values 0) - (Znth i b_data 0) )) ” 
  &&  “ (((Znth i values 0) - (Znth i b_data 0) ) > 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing_2: (@list (Z * Z))) (increasing_2: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) > 0)) (PreH2 : (((Znth i values 0) - (Znth i b_data 0) ) >= 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH9 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= nx)) (PreH13 : (nx <= i)) (PreH14 : (0 <= ny)) (PreH15 : (ny <= i)) (PreH16 : ((Zlength (increasing_2)) = nx)) (PreH17 : ((Zlength (decreasing_2)) = ny)) (PreH18 : (0 <= base)) (PreH19 : (base <= (999999999 * i ))) (PreH20 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH21 : (SegmentsBounded increasing_2 )) (PreH22 : (SegmentsBounded decreasing_2 )) ,
  (SegArray.full x nx increasing_2 )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_2 )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (x_3: Z)  (x_2: Z)  (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (((Znth i values 0) - (Znth i b_data 0) ) > 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> x_3)
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> x_2)
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
).

Definition solver_entail_wit_4_1 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_2: (@list (Z * Z))) (decreasing_2: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing_2)) = nx)) (PreH14 : ((Zlength (decreasing_2)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d < 0)) (PreH19 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH20 : (SegmentsBounded increasing_2 )) (PreH21 : (SegmentsBounded decreasing_2 )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing_2 )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i values 0))
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i b_data 0))
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing_2 )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (nx + 1 )) ” 
  &&  “ ((nx + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= (i + 1 )) ” 
  &&  “ ((Zlength (increasing)) = (nx + 1 )) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= (base - d )) ” 
  &&  “ ((base - d ) <= (999999999 * (i + 1 ) )) ” 
  &&  “ (SolverScanState values b_data (i + 1 ) (base - d ) increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x (nx + 1 ) increasing )
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) (n_pre - (nx + 1 ) ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_2: (@list (Z * Z))) (decreasing_2: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : ((Znth i b_data 0) <= INT_MAX)) (PreH2 : ((Znth i values 0) <= INT_MAX)) (PreH3 : ((Znth i b_data 0) >= INT_MIN)) (PreH4 : ((Znth i values 0) >= INT_MIN)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (b_data)) = (Zlength (values)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= nx)) (PreH14 : (nx <= i)) (PreH15 : (0 <= ny)) (PreH16 : (ny <= i)) (PreH17 : ((Zlength (increasing_2)) = nx)) (PreH18 : ((Zlength (decreasing_2)) = ny)) (PreH19 : (0 <= base)) (PreH20 : (base <= (999999999 * i ))) (PreH21 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH22 : (d < 0)) (PreH23 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH24 : (SegmentsBounded increasing_2 )) (PreH25 : (SegmentsBounded decreasing_2 )) ,
  (SegArray.full x nx increasing_2 )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i values 0))
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i b_data 0))
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing_2 )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (nx + 1 )) ” 
  &&  “ ((nx + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= (i + 1 )) ” 
  &&  “ ((Zlength (increasing)) = (nx + 1 )) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= (base - d )) ” 
  &&  “ ((base - d ) <= (999999999 * (i + 1 ) )) ” 
  &&  “ (SolverScanState values b_data (i + 1 ) (base - d ) increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (SegArray.full x (nx + 1 ) increasing )
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) (n_pre - (nx + 1 ) ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
).

Definition solver_entail_wit_4_2 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_2: (@list (Z * Z))) (decreasing_2: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing_2)) = nx)) (PreH14 : ((Zlength (decreasing_2)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d > 0)) (PreH19 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH20 : (SegmentsBounded increasing_2 )) (PreH21 : (SegmentsBounded decreasing_2 )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing_2 )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_2 )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i b_data 0))
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i values 0))
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= (i + 1 )) ” 
  &&  “ (0 <= (ny + 1 )) ” 
  &&  “ ((ny + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = (ny + 1 )) ” 
  &&  “ (0 <= (base + d )) ” 
  &&  “ ((base + d ) <= (999999999 * (i + 1 ) )) ” 
  &&  “ (SolverScanState values b_data (i + 1 ) (base + d ) increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y (ny + 1 ) decreasing )
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) (n_pre - (ny + 1 ) ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_2: (@list (Z * Z))) (decreasing_2: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : ((Znth i values 0) <= INT_MAX)) (PreH2 : ((Znth i b_data 0) <= INT_MAX)) (PreH3 : ((Znth i values 0) >= INT_MIN)) (PreH4 : ((Znth i b_data 0) >= INT_MIN)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : ((Zlength (b_data)) = (Zlength (values)))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : (0 <= nx)) (PreH14 : (nx <= i)) (PreH15 : (0 <= ny)) (PreH16 : (ny <= i)) (PreH17 : ((Zlength (increasing_2)) = nx)) (PreH18 : ((Zlength (decreasing_2)) = ny)) (PreH19 : (0 <= base)) (PreH20 : (base <= (999999999 * i ))) (PreH21 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH22 : (d > 0)) (PreH23 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH24 : (SegmentsBounded increasing_2 )) (PreH25 : (SegmentsBounded decreasing_2 )) ,
  (SegArray.full x nx increasing_2 )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_2 )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i b_data 0))
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |-> (Znth i values 0))
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= (i + 1 )) ” 
  &&  “ (0 <= (ny + 1 )) ” 
  &&  “ ((ny + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = (ny + 1 )) ” 
  &&  “ (0 <= (base + d )) ” 
  &&  “ ((base + d ) <= (999999999 * (i + 1 ) )) ” 
  &&  “ (SolverScanState values b_data (i + 1 ) (base + d ) increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y (ny + 1 ) decreasing )
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) (n_pre - (ny + 1 ) ) )
).

Definition solver_entail_wit_4_3 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing_2: (@list (Z * Z))) (increasing_2: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) <= 0)) (PreH2 : (((Znth i values 0) - (Znth i b_data 0) ) >= 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= nx)) (PreH13 : (nx <= i)) (PreH14 : (0 <= ny)) (PreH15 : (ny <= i)) (PreH16 : ((Zlength (increasing_2)) = nx)) (PreH17 : ((Zlength (decreasing_2)) = ny)) (PreH18 : (0 <= base)) (PreH19 : (base <= (999999999 * i ))) (PreH20 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH21 : (SegmentsBounded increasing_2 )) (PreH22 : (SegmentsBounded decreasing_2 )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing_2 )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_2 )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (decreasing: (@list (Z * Z)))  (increasing: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= (i + 1 )) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= (i + 1 )) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * (i + 1 ) )) ” 
  &&  “ (SolverScanState values b_data (i + 1 ) base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (base: Z) (decreasing_2: (@list (Z * Z))) (increasing_2: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) <= 0)) (PreH2 : (((Znth i values 0) - (Znth i b_data 0) ) >= 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= nx)) (PreH13 : (nx <= i)) (PreH14 : (0 <= ny)) (PreH15 : (ny <= i)) (PreH16 : ((Zlength (increasing_2)) = nx)) (PreH17 : ((Zlength (decreasing_2)) = ny)) (PreH18 : (0 <= base)) (PreH19 : (base <= (999999999 * i ))) (PreH20 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH21 : (SegmentsBounded increasing_2 )) (PreH22 : (SegmentsBounded decreasing_2 )) ,
  TT && emp 
|--
  “ (SolverScanState values b_data (i + 1 ) base increasing_2 decreasing_2 ) ”
  &&  emp
).

Definition solver_entail_wit_4_3_split_goal_1 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (base: Z) (decreasing_2: (@list (Z * Z))) (increasing_2: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (((Znth i values 0) - (Znth i b_data 0) ) <= 0)) (PreH2 : (((Znth i values 0) - (Znth i b_data 0) ) >= 0)) (PreH3 : (i < n_pre)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= nx)) (PreH13 : (nx <= i)) (PreH14 : (0 <= ny)) (PreH15 : (ny <= i)) (PreH16 : ((Zlength (increasing_2)) = nx)) (PreH17 : ((Zlength (decreasing_2)) = ny)) (PreH18 : (0 <= base)) (PreH19 : (base <= (999999999 * i ))) (PreH20 : (SolverScanState values b_data i base increasing_2 decreasing_2 )) (PreH21 : (SegmentsBounded increasing_2 )) (PreH22 : (SegmentsBounded decreasing_2 )) ,
  (SolverScanState values b_data (i + 1 ) base increasing_2 decreasing_2 )
.

Definition solver_entail_wit_5 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= n_pre) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= n_pre) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * n_pre )) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny (DecreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny (DecreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) ) ”
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) ) ”
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (base = (PairDistanceSum (values) (b_data))) ”
.

Definition solver_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre))))) ”
.

Definition solver_entail_wit_5_split_goal_5 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre))))) ”
.

Definition solver_entail_wit_5_split_goal_6 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ”
.

Definition solver_entail_wit_5_split_goal_7 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
.

Definition solver_entail_wit_5_split_goal_spatial := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH7 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 b_data 0)) /\ ((Znth k_4 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny (DecreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
.

Definition solver_entail_wit_6_1 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (x: Z) (y: Z) (right_after: (@list (Z * Z))) (retval: Z) (right_after_2: (@list (Z * Z))) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval_2 )) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval )) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (SegArray.full y ny right_after )
  **  (SegArray.full x nx right_after_2 )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (decreasing_after: (@list (Z * Z)))  (increasing_after: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * n_pre )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1000000000) ” 
  &&  “ (SwappingOverlapMaximum values b_data retval ) ” 
  &&  “ (Spec values b_data (base - (2 * retval ) ) ) ” 
  &&  “ ((Zlength (increasing_after)) = nx) ” 
  &&  “ ((Zlength (decreasing_after)) = ny) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (right_after: (@list (Z * Z))) (retval: Z) (right_after_2: (@list (Z * Z))) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval_2 )) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval )) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  TT && emp 
|--
  “ (Spec values b_data (base - (2 * retval ) ) ) ” 
  &&  “ (SwappingOverlapMaximum values b_data retval ) ”
  &&  emp
).

Definition solver_entail_wit_6_1_split_goal_1 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (right_after: (@list (Z * Z))) (retval: Z) (right_after_2: (@list (Z * Z))) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval_2 )) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval )) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (Spec values b_data (base - (2 * retval ) ) )
.

Definition solver_entail_wit_6_1_split_goal_2 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (right_after: (@list (Z * Z))) (retval: Z) (right_after_2: (@list (Z * Z))) (retval_2: Z) (PreH1 : (retval > retval_2)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval_2 )) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval )) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (SwappingOverlapMaximum values b_data retval )
.

Definition solver_entail_wit_6_2 := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (x: Z) (y: Z) (right_after: (@list (Z * Z))) (retval_2: Z) (right_after_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval_2 <= retval)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval_2 )) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (SegArray.full y ny right_after )
  **  (SegArray.full x nx right_after_2 )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  EX (decreasing_after: (@list (Z * Z)))  (increasing_after: (@list (Z * Z))) ,
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * n_pre )) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1000000000) ” 
  &&  “ (SwappingOverlapMaximum values b_data retval ) ” 
  &&  “ (Spec values b_data (base - (2 * retval ) ) ) ” 
  &&  “ ((Zlength (increasing_after)) = nx) ” 
  &&  “ ((Zlength (decreasing_after)) = ny) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
) \/
(
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (right_after: (@list (Z * Z))) (retval_2: Z) (right_after_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval_2 <= retval)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval_2 )) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  TT && emp 
|--
  “ (Spec values b_data (base - (2 * retval ) ) ) ” 
  &&  “ (SwappingOverlapMaximum values b_data retval ) ”
  &&  emp
).

Definition solver_entail_wit_6_2_split_goal_1 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (right_after: (@list (Z * Z))) (retval_2: Z) (right_after_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval_2 <= retval)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval_2 )) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (Spec values b_data (base - (2 * retval ) ) )
.

Definition solver_entail_wit_6_2_split_goal_2 := 
forall (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (right_after: (@list (Z * Z))) (retval_2: Z) (right_after_2: (@list (Z * Z))) (retval: Z) (PreH1 : (retval_2 <= retval)) (PreH2 : ((Zlength (right_after_2)) = nx)) (PreH3 : (Permutation (IncreasingIntervals (values) (b_data) ((Zlength (values)))) right_after_2 )) (PreH4 : (SegmentsBounded right_after_2 )) (PreH5 : (DirectedOverlapMaximum right_after (IncreasingIntervals (values) (b_data) ((Zlength (values)))) retval )) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1000000000)) (PreH8 : ((Zlength (right_after)) = ny)) (PreH9 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH10 : (SegmentsBounded right_after )) (PreH11 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval_2 )) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1000000000)) (PreH14 : (n_pre = (Zlength (values)))) (PreH15 : ((Zlength (b_data)) = (Zlength (values)))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 200000)) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH20 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH21 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH22 : (0 <= nx)) (PreH23 : (nx <= n_pre)) (PreH24 : (0 <= ny)) (PreH25 : (ny <= n_pre)) (PreH26 : (0 <= base)) (PreH27 : (base <= (999999999 * n_pre ))) (PreH28 : (base = (PairDistanceSum (values) (b_data)))) (PreH29 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH30 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (SwappingOverlapMaximum values b_data retval )
.

Definition solver_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (Spec values b_data (base - (2 * best ) ) ) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
.

Definition solver_partial_solve_wit_1_pure := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : ((Zlength (b_data)) = (Zlength (values)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))) ,
  ((( &( "y" ) )) # Ptr  |->_)
  **  (SegArray.undef_full retval n_pre )
  **  ((( &( "x" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= n_pre) ” 
  &&  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : ((Zlength (b_data)) = (Zlength (values)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))) ,
  ((( &( "y" ) )) # Ptr  |->_)
  **  (SegArray.undef_full retval n_pre )
  **  ((( &( "x" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= (Zlength (values)))) (PreH5 : ((Zlength (values)) <= 200000)) (PreH6 : ((Zlength (b_data)) = (Zlength (values)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH9 : (n_pre = (Zlength (values)))) ,
  ((( &( "y" ) )) # Ptr  |->_)
  **  (SegArray.undef_full retval n_pre )
  **  ((( &( "x" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (1 <= (Zlength (values)))) (PreH3 : ((Zlength (values)) <= 200000)) (PreH4 : ((Zlength (b_data)) = (Zlength (values)))) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH7 : (n_pre = (Zlength (values)))) ,
  (SegArray.undef_full retval n_pre )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= n_pre) ” 
  &&  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (1 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 200000) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (SegArray.undef_full retval n_pre )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 200000)) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  ((( &( "x" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= n_pre) ” 
  &&  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((( &( "x" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (1 <= (Zlength (values)))) (PreH4 : ((Zlength (values)) <= 200000)) (PreH5 : ((Zlength (b_data)) = (Zlength (values)))) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH8 : (n_pre = (Zlength (values)))) ,
  ((( &( "x" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (PreH1 : (1 <= (Zlength (values)))) (PreH2 : ((Zlength (values)) <= 200000)) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
|--
  “ (0 <= n_pre) ” 
  &&  “ (SegmentAllocationSize (n_pre * sizeof( "<anonymous struct>" ) ) n_pre ) ” 
  &&  “ (1 <= (Zlength (values))) ” 
  &&  “ ((Zlength (values)) <= 200000) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (values)))) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (Zlength (b_data)))) -> ((1 <= (Znth i_2 b_data 0)) /\ ((Znth i_2 b_data 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
.

Definition solver_partial_solve_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (y: Z) (x: Z) (base: Z) (decreasing: (@list (Z * Z))) (increasing: (@list (Z * Z))) (ny: Z) (nx: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (values)))) (PreH3 : ((Zlength (b_data)) = (Zlength (values)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= nx)) (PreH11 : (nx <= i)) (PreH12 : (0 <= ny)) (PreH13 : (ny <= i)) (PreH14 : ((Zlength (increasing)) = nx)) (PreH15 : ((Zlength (decreasing)) = ny)) (PreH16 : (0 <= base)) (PreH17 : (base <= (999999999 * i ))) (PreH18 : (SolverScanState values b_data i base increasing decreasing )) (PreH19 : (SegmentsBounded increasing )) (PreH20 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i b_data 0))
  **  (IntArray.missing_i b_pre i 0 n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
.

Definition solver_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d < 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (d = ((Znth i values 0) - (Znth i b_data 0) )) ” 
  &&  “ (d < 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
.

Definition solver_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d < 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i values 0))
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (d = ((Znth i values 0) - (Znth i b_data 0) )) ” 
  &&  “ (d < 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i b_data 0))
  **  (IntArray.missing_i b_pre i 0 n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing )
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i values 0))
  **  ((&(((x + (nx * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (x + ((nx + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - nx ) - 1 ) )
  **  (SegArray.full y ny decreasing )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
.

Definition solver_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d > 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (d = ((Znth i values 0) - (Znth i b_data 0) )) ” 
  &&  “ (d > 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> (Znth i b_data 0))
  **  (IntArray.missing_i b_pre i 0 n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |->_)
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
.

Definition solver_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing: (@list (Z * Z))) (decreasing: (@list (Z * Z))) (i: Z) (nx: Z) (ny: Z) (base: Z) (d: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= nx)) (PreH10 : (nx <= i)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= i)) (PreH13 : ((Zlength (increasing)) = nx)) (PreH14 : ((Zlength (decreasing)) = ny)) (PreH15 : (0 <= base)) (PreH16 : (base <= (999999999 * i ))) (PreH17 : (d = ((Znth i values 0) - (Znth i b_data 0) ))) (PreH18 : (d > 0)) (PreH19 : (SolverScanState values b_data i base increasing decreasing )) (PreH20 : (SegmentsBounded increasing )) (PreH21 : (SegmentsBounded decreasing )) ,
  (IntArray.full b_pre n_pre b_data )
  **  (IntArray.full a_pre n_pre values )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i b_data 0))
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
|--
  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= i) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= i) ” 
  &&  “ ((Zlength (increasing)) = nx) ” 
  &&  “ ((Zlength (decreasing)) = ny) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * i )) ” 
  &&  “ (d = ((Znth i values 0) - (Znth i b_data 0) )) ” 
  &&  “ (d > 0) ” 
  &&  “ (SolverScanState values b_data i base increasing decreasing ) ” 
  &&  “ (SegmentsBounded increasing ) ” 
  &&  “ (SegmentsBounded decreasing ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i a_pre i 0 n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing )
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "l")) # Int  |-> (Znth i b_data 0))
  **  ((&(((y + (ny * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "r")) # Int  |->_)
  **  (SegArray.undef_full (y + ((ny + 1 ) * sizeof( "<anonymous struct>" ))) ((n_pre - ny ) - 1 ) )
.

Definition solver_partial_solve_wit_9_pure := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (x: Z) (y: Z) (right_after: (@list (Z * Z))) (retval: Z) (PreH1 : ((Zlength (right_after)) = ny)) (PreH2 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH3 : (SegmentsBounded right_after )) (PreH4 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1000000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (b_data)) = (Zlength (values)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH13 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH14 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH15 : (0 <= nx)) (PreH16 : (nx <= n_pre)) (PreH17 : (0 <= ny)) (PreH18 : (ny <= n_pre)) (PreH19 : (0 <= base)) (PreH20 : (base <= (999999999 * n_pre ))) (PreH21 : (base = (PairDistanceSum (values) (b_data)))) (PreH22 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH23 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  ((( &( "q" ) )) # Int  |->_)
  **  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.full y ny right_after )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (ny = (Zlength (right_after))) ” 
  &&  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) ((Zlength (values))))))) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= 200000) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= 200000) ” 
  &&  “ (SegmentsBounded right_after ) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) ((Zlength (values)))) ) ”
.

Definition solver_partial_solve_wit_9_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (x: Z) (y: Z) (right_after: (@list (Z * Z))) (retval: Z) (PreH1 : ((Zlength (right_after)) = ny)) (PreH2 : (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after )) (PreH3 : (SegmentsBounded right_after )) (PreH4 : (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1000000000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : ((Zlength (b_data)) = (Zlength (values)))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH13 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH14 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH15 : (0 <= nx)) (PreH16 : (nx <= n_pre)) (PreH17 : (0 <= ny)) (PreH18 : (ny <= n_pre)) (PreH19 : (0 <= base)) (PreH20 : (base <= (999999999 * n_pre ))) (PreH21 : (base = (PairDistanceSum (values) (b_data)))) (PreH22 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH23 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.full y ny right_after )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (ny = (Zlength (right_after))) ” 
  &&  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) ((Zlength (values))))))) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= 200000) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= 200000) ” 
  &&  “ (SegmentsBounded right_after ) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) ((Zlength (values)))) ) ” 
  &&  “ ((Zlength (right_after)) = ny) ” 
  &&  “ (Permutation (DecreasingIntervals (values) (b_data) (n_pre)) right_after ) ” 
  &&  “ (SegmentsBounded right_after ) ” 
  &&  “ (DirectedOverlapMaximum (IncreasingIntervals (values) (b_data) (n_pre)) (DecreasingIntervals (values) (b_data) (n_pre)) retval ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1000000000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= n_pre) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= n_pre) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * n_pre )) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) ) ”
  &&  (SegArray.full y ny right_after )
  **  (SegArray.full x nx (IncreasingIntervals (values) (b_data) ((Zlength (values)))) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
.

Definition solver_partial_solve_wit_9 := solver_partial_solve_wit_9_pure -> solver_partial_solve_wit_9_aux.

Definition solver_partial_solve_wit_10_pure := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH8 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH9 : (0 <= nx)) (PreH10 : (nx <= n_pre)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= n_pre)) (PreH13 : (0 <= base)) (PreH14 : (base <= (999999999 * n_pre ))) (PreH15 : (base = (PairDistanceSum (values) (b_data)))) (PreH16 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH17 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny (DecreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= 200000) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= 200000) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) ) ”
.

Definition solver_partial_solve_wit_10_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (nx: Z) (ny: Z) (base: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000)))) (PreH7 : (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre)))))) (PreH8 : (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre)))))) (PreH9 : (0 <= nx)) (PreH10 : (nx <= n_pre)) (PreH11 : (0 <= ny)) (PreH12 : (ny <= n_pre)) (PreH13 : (0 <= base)) (PreH14 : (base <= (999999999 * n_pre ))) (PreH15 : (base = (PairDistanceSum (values) (b_data)))) (PreH16 : (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) )) (PreH17 : (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) )) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny (DecreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= 200000) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= 200000) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 b_data 0)) /\ ((Znth k_2 b_data 0) <= 1000000000))) ” 
  &&  “ (nx = (Zlength ((IncreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (ny = (Zlength ((DecreasingIntervals (values) (b_data) (n_pre))))) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (nx <= n_pre) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (ny <= n_pre) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * n_pre )) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (SegmentsBounded (IncreasingIntervals (values) (b_data) (n_pre)) ) ” 
  &&  “ (SegmentsBounded (DecreasingIntervals (values) (b_data) (n_pre)) ) ”
  &&  (SegArray.full x nx (IncreasingIntervals (values) (b_data) (n_pre)) )
  **  (SegArray.full y ny (DecreasingIntervals (values) (b_data) (n_pre)) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
.

Definition solver_partial_solve_wit_10 := solver_partial_solve_wit_10_pure -> solver_partial_solve_wit_10_aux.

Definition solver_partial_solve_wit_11_pure := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ ((Zlength (decreasing_after)) = ny) ” 
  &&  “ (ny <= n_pre) ” 
  &&  “ (0 <= ny) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (base <= INT64_MAX)) (PreH2 : (base >= INT64_MIN)) (PreH3 : (q_addr_v <= INT_MAX)) (PreH4 : (p_addr_v <= INT_MAX)) (PreH5 : (ny <= INT_MAX)) (PreH6 : (nx <= INT_MAX)) (PreH7 : (best <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (q_addr_v >= INT_MIN)) (PreH10 : (p_addr_v >= INT_MIN)) (PreH11 : (ny >= INT_MIN)) (PreH12 : (nx >= INT_MIN)) (PreH13 : (best >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : ((Zlength (b_data)) = (Zlength (values)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (base = (PairDistanceSum (values) (b_data)))) (PreH20 : (0 <= base)) (PreH21 : (base <= (999999999 * n_pre ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : (SwappingOverlapMaximum values b_data best )) (PreH25 : (Spec values b_data (base - (2 * best ) ) )) (PreH26 : ((Zlength (increasing_after)) = nx)) (PreH27 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (0 <= ny) ” 
  &&  “ (ny <= n_pre) ”
).

Definition solver_partial_solve_wit_11_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (base <= INT64_MAX)) (PreH2 : (base >= INT64_MIN)) (PreH3 : (q_addr_v <= INT_MAX)) (PreH4 : (p_addr_v <= INT_MAX)) (PreH5 : (ny <= INT_MAX)) (PreH6 : (nx <= INT_MAX)) (PreH7 : (best <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (q_addr_v >= INT_MIN)) (PreH10 : (p_addr_v >= INT_MIN)) (PreH11 : (ny >= INT_MIN)) (PreH12 : (nx >= INT_MIN)) (PreH13 : (best >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : ((Zlength (b_data)) = (Zlength (values)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (base = (PairDistanceSum (values) (b_data)))) (PreH20 : (0 <= base)) (PreH21 : (base <= (999999999 * n_pre ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : (SwappingOverlapMaximum values b_data best )) (PreH25 : (Spec values b_data (base - (2 * best ) ) )) (PreH26 : ((Zlength (increasing_after)) = nx)) (PreH27 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (0 <= ny) ”
.

Definition solver_partial_solve_wit_11_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (base <= INT64_MAX)) (PreH2 : (base >= INT64_MIN)) (PreH3 : (q_addr_v <= INT_MAX)) (PreH4 : (p_addr_v <= INT_MAX)) (PreH5 : (ny <= INT_MAX)) (PreH6 : (nx <= INT_MAX)) (PreH7 : (best <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (q_addr_v >= INT_MIN)) (PreH10 : (p_addr_v >= INT_MIN)) (PreH11 : (ny >= INT_MIN)) (PreH12 : (nx >= INT_MIN)) (PreH13 : (best >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : ((Zlength (b_data)) = (Zlength (values)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (base = (PairDistanceSum (values) (b_data)))) (PreH20 : (0 <= base)) (PreH21 : (base <= (999999999 * n_pre ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : (SwappingOverlapMaximum values b_data best )) (PreH25 : (Spec values b_data (base - (2 * best ) ) )) (PreH26 : ((Zlength (increasing_after)) = nx)) (PreH27 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ (ny <= n_pre) ”
.

Definition solver_partial_solve_wit_11_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
|--
  “ ((Zlength (decreasing_after)) = ny) ” 
  &&  “ (ny <= n_pre) ” 
  &&  “ (0 <= ny) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * n_pre )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ (SwappingOverlapMaximum values b_data best ) ” 
  &&  “ (Spec values b_data (base - (2 * best ) ) ) ” 
  &&  “ ((Zlength (increasing_after)) = nx) ” 
  &&  “ ((Zlength (decreasing_after)) = ny) ”
  &&  (SegArray.full y ny decreasing_after )
  **  (SegArray.undef_full (y + (ny * sizeof( "<anonymous struct>" ))) (n_pre - ny ) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
.

Definition solver_partial_solve_wit_11 := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux.

Definition solver_partial_solve_wit_12_pure := 
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  “ ((Zlength (increasing_after)) = nx) ” 
  &&  “ (nx <= n_pre) ” 
  &&  “ (0 <= nx) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (base <= INT64_MAX)) (PreH2 : (base >= INT64_MIN)) (PreH3 : (q_addr_v <= INT_MAX)) (PreH4 : (p_addr_v <= INT_MAX)) (PreH5 : (ny <= INT_MAX)) (PreH6 : (nx <= INT_MAX)) (PreH7 : (best <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (q_addr_v >= INT_MIN)) (PreH10 : (p_addr_v >= INT_MIN)) (PreH11 : (ny >= INT_MIN)) (PreH12 : (nx >= INT_MIN)) (PreH13 : (best >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : ((Zlength (b_data)) = (Zlength (values)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (base = (PairDistanceSum (values) (b_data)))) (PreH20 : (0 <= base)) (PreH21 : (base <= (999999999 * n_pre ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : (SwappingOverlapMaximum values b_data best )) (PreH25 : (Spec values b_data (base - (2 * best ) ) )) (PreH26 : ((Zlength (increasing_after)) = nx)) (PreH27 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  “ (0 <= nx) ” 
  &&  “ (nx <= n_pre) ”
).

Definition solver_partial_solve_wit_12_pure_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (base <= INT64_MAX)) (PreH2 : (base >= INT64_MIN)) (PreH3 : (q_addr_v <= INT_MAX)) (PreH4 : (p_addr_v <= INT_MAX)) (PreH5 : (ny <= INT_MAX)) (PreH6 : (nx <= INT_MAX)) (PreH7 : (best <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (q_addr_v >= INT_MIN)) (PreH10 : (p_addr_v >= INT_MIN)) (PreH11 : (ny >= INT_MIN)) (PreH12 : (nx >= INT_MIN)) (PreH13 : (best >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : ((Zlength (b_data)) = (Zlength (values)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (base = (PairDistanceSum (values) (b_data)))) (PreH20 : (0 <= base)) (PreH21 : (base <= (999999999 * n_pre ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : (SwappingOverlapMaximum values b_data best )) (PreH25 : (Spec values b_data (base - (2 * best ) ) )) (PreH26 : ((Zlength (increasing_after)) = nx)) (PreH27 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  “ (0 <= nx) ”
.

Definition solver_partial_solve_wit_12_pure_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (p_addr_v: Z) (q_addr_v: Z) (x: Z) (y: Z) (PreH1 : (base <= INT64_MAX)) (PreH2 : (base >= INT64_MIN)) (PreH3 : (q_addr_v <= INT_MAX)) (PreH4 : (p_addr_v <= INT_MAX)) (PreH5 : (ny <= INT_MAX)) (PreH6 : (nx <= INT_MAX)) (PreH7 : (best <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (q_addr_v >= INT_MIN)) (PreH10 : (p_addr_v >= INT_MIN)) (PreH11 : (ny >= INT_MIN)) (PreH12 : (nx >= INT_MIN)) (PreH13 : (best >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (n_pre = (Zlength (values)))) (PreH16 : ((Zlength (b_data)) = (Zlength (values)))) (PreH17 : (1 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (base = (PairDistanceSum (values) (b_data)))) (PreH20 : (0 <= base)) (PreH21 : (base <= (999999999 * n_pre ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 1000000000)) (PreH24 : (SwappingOverlapMaximum values b_data best )) (PreH25 : (Spec values b_data (base - (2 * best ) ) )) (PreH26 : ((Zlength (increasing_after)) = nx)) (PreH27 : ((Zlength (decreasing_after)) = ny)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "base" ) )) # Int64  |-> base)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "nx" ) )) # Int  |-> nx)
  **  ((( &( "ny" ) )) # Int  |-> ny)
  **  ((( &( "p" ) )) # Int  |-> p_addr_v)
  **  ((( &( "q" ) )) # Int  |-> q_addr_v)
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  “ (nx <= n_pre) ”
.

Definition solver_partial_solve_wit_12_aux := 
forall (b_pre: Z) (a_pre: Z) (n_pre: Z) (b_data: (@list Z)) (values: (@list Z)) (increasing_after: (@list (Z * Z))) (decreasing_after: (@list (Z * Z))) (base: Z) (best: Z) (nx: Z) (ny: Z) (x: Z) (PreH1 : (n_pre = (Zlength (values)))) (PreH2 : ((Zlength (b_data)) = (Zlength (values)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (base = (PairDistanceSum (values) (b_data)))) (PreH6 : (0 <= base)) (PreH7 : (base <= (999999999 * n_pre ))) (PreH8 : (0 <= best)) (PreH9 : (best <= 1000000000)) (PreH10 : (SwappingOverlapMaximum values b_data best )) (PreH11 : (Spec values b_data (base - (2 * best ) ) )) (PreH12 : ((Zlength (increasing_after)) = nx)) (PreH13 : ((Zlength (decreasing_after)) = ny)) ,
  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
  **  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
|--
  “ ((Zlength (increasing_after)) = nx) ” 
  &&  “ (nx <= n_pre) ” 
  &&  “ (0 <= nx) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ ((Zlength (b_data)) = (Zlength (values))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (base = (PairDistanceSum (values) (b_data))) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= (999999999 * n_pre )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 1000000000) ” 
  &&  “ (SwappingOverlapMaximum values b_data best ) ” 
  &&  “ (Spec values b_data (base - (2 * best ) ) ) ” 
  &&  “ ((Zlength (increasing_after)) = nx) ” 
  &&  “ ((Zlength (decreasing_after)) = ny) ”
  &&  (SegArray.full x nx increasing_after )
  **  (SegArray.undef_full (x + (nx * sizeof( "<anonymous struct>" ))) (n_pre - nx ) )
  **  (IntArray.full a_pre n_pre values )
  **  (IntArray.full b_pre n_pre b_data )
.

Definition solver_partial_solve_wit_12 := solver_partial_solve_wit_12_pure -> solver_partial_solve_wit_12_aux.

Module Type VC_Correct.


Axiom proof_of_overlap_safety_wit_1 : overlap_safety_wit_1.
Axiom proof_of_overlap_safety_wit_2 : overlap_safety_wit_2.
Axiom proof_of_overlap_safety_wit_3 : overlap_safety_wit_3.
Axiom proof_of_overlap_safety_wit_4 : overlap_safety_wit_4.
Axiom proof_of_overlap_safety_wit_5 : overlap_safety_wit_5.
Axiom proof_of_overlap_safety_wit_6 : overlap_safety_wit_6.
Axiom proof_of_overlap_safety_wit_7 : overlap_safety_wit_7.
Axiom proof_of_overlap_safety_wit_8 : overlap_safety_wit_8.
Axiom proof_of_overlap_safety_wit_9 : overlap_safety_wit_9.
Axiom proof_of_overlap_safety_wit_10 : overlap_safety_wit_10.
Axiom proof_of_overlap_safety_wit_11 : overlap_safety_wit_11.
Axiom proof_of_overlap_safety_wit_12 : overlap_safety_wit_12.
Axiom proof_of_overlap_safety_wit_13 : overlap_safety_wit_13.
Axiom proof_of_overlap_safety_wit_14 : overlap_safety_wit_14.
Axiom proof_of_overlap_safety_wit_15 : overlap_safety_wit_15.
Axiom proof_of_overlap_safety_wit_16 : overlap_safety_wit_16.
Axiom proof_of_overlap_safety_wit_17 : overlap_safety_wit_17.
Axiom proof_of_overlap_safety_wit_18 : overlap_safety_wit_18.
Axiom proof_of_overlap_safety_wit_19 : overlap_safety_wit_19.
Axiom proof_of_overlap_safety_wit_20 : overlap_safety_wit_20.
Axiom proof_of_overlap_safety_wit_21 : overlap_safety_wit_21.
Axiom proof_of_overlap_safety_wit_22 : overlap_safety_wit_22.
Axiom proof_of_overlap_safety_wit_23 : overlap_safety_wit_23.
Axiom proof_of_overlap_safety_wit_24 : overlap_safety_wit_24.
Axiom proof_of_overlap_safety_wit_25 : overlap_safety_wit_25.
Axiom proof_of_overlap_safety_wit_26 : overlap_safety_wit_26.
Axiom proof_of_overlap_safety_wit_27 : overlap_safety_wit_27.
Axiom proof_of_overlap_safety_wit_28 : overlap_safety_wit_28.
Axiom proof_of_overlap_safety_wit_29 : overlap_safety_wit_29.
Axiom proof_of_overlap_entail_wit_1 : overlap_entail_wit_1.
Axiom proof_of_overlap_entail_wit_2 : overlap_entail_wit_2.
Axiom proof_of_overlap_entail_wit_3_1 : overlap_entail_wit_3_1.
Axiom proof_of_overlap_entail_wit_3_2 : overlap_entail_wit_3_2.
Axiom proof_of_overlap_entail_wit_3_3 : overlap_entail_wit_3_3.
Axiom proof_of_overlap_entail_wit_4 : overlap_entail_wit_4.
Axiom proof_of_overlap_entail_wit_5 : overlap_entail_wit_5.
Axiom proof_of_overlap_entail_wit_6 : overlap_entail_wit_6.
Axiom proof_of_overlap_entail_wit_7_1 : overlap_entail_wit_7_1.
Axiom proof_of_overlap_entail_wit_7_2 : overlap_entail_wit_7_2.
Axiom proof_of_overlap_entail_wit_8 : overlap_entail_wit_8.
Axiom proof_of_overlap_entail_wit_9_1 : overlap_entail_wit_9_1.
Axiom proof_of_overlap_entail_wit_9_2 : overlap_entail_wit_9_2.
Axiom proof_of_overlap_entail_wit_9_3 : overlap_entail_wit_9_3.
Axiom proof_of_overlap_entail_wit_9_4 : overlap_entail_wit_9_4.
Axiom proof_of_overlap_entail_wit_9_5 : overlap_entail_wit_9_5.
Axiom proof_of_overlap_return_wit_1 : overlap_return_wit_1.
Axiom proof_of_overlap_return_wit_2 : overlap_return_wit_2.
Axiom proof_of_overlap_return_wit_3 : overlap_return_wit_3.
Axiom proof_of_overlap_partial_solve_wit_1_pure : overlap_partial_solve_wit_1_pure.
Axiom proof_of_overlap_partial_solve_wit_1 : overlap_partial_solve_wit_1.
Axiom proof_of_overlap_partial_solve_wit_2_pure : overlap_partial_solve_wit_2_pure.
Axiom proof_of_overlap_partial_solve_wit_2 : overlap_partial_solve_wit_2.
Axiom proof_of_overlap_partial_solve_wit_3 : overlap_partial_solve_wit_3.
Axiom proof_of_overlap_partial_solve_wit_4 : overlap_partial_solve_wit_4.
Axiom proof_of_overlap_partial_solve_wit_5 : overlap_partial_solve_wit_5.
Axiom proof_of_overlap_partial_solve_wit_6 : overlap_partial_solve_wit_6.
Axiom proof_of_overlap_partial_solve_wit_7_pure : overlap_partial_solve_wit_7_pure.
Axiom proof_of_overlap_partial_solve_wit_7 : overlap_partial_solve_wit_7.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9_pure : solver_partial_solve_wit_9_pure.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10_pure : solver_partial_solve_wit_10_pure.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.

End VC_Correct.
