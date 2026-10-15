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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P061_2042C_competitive_fishing_lib.
Local Open Scope sac.

(*----- Function cmp_desc -----*)

Definition cmp_desc_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (b: Z) (a: Z) (PreH1 : (b >= a)) (PreH2 : (b > a)) ,
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
|--
  “ ((1 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition cmp_desc_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (b: Z) (a: Z) (PreH1 : (b < a)) (PreH2 : (b <= a)) ,
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
|--
  “ ((0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 1 )) ”
.

Definition cmp_desc_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (b: Z) (a: Z) (PreH1 : (b >= a)) (PreH2 : (b <= a)) ,
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
|--
  “ ((0 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition cmp_desc_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (b: Z) (a: Z) (PreH1 : (b < a)) (PreH2 : (b > a)) ,
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
|--
  “ False ”
.

Definition cmp_desc_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (b: Z) (a: Z) (PreH1 : (b >= a)) (PreH2 : (b <= a)) ,
  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
|--
  “ (b = a) ” 
  &&  “ ((0 - 0 ) = 0) ”
  &&  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
.

Definition cmp_desc_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (b: Z) (a: Z) (PreH1 : (b < a)) (PreH2 : (b <= a)) ,
  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
|--
  “ (b < a) ” 
  &&  “ ((0 - 1 ) = (-1)) ”
  &&  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
.

Definition cmp_desc_return_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (b: Z) (a: Z) (PreH1 : (b >= a)) (PreH2 : (b > a)) ,
  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
|--
  “ (b > a) ” 
  &&  “ ((1 - 0 ) = 1) ”
  &&  ((x_pre) # Int  |-> a)
  **  ((y_pre) # Int  |-> b)
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (f)))) (PreH3 : ((Zlength (f)) <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH7 : (n_pre = (Zlength (f)))) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_2 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (f)))) (PreH3 : ((Zlength (f)) <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH7 : (n_pre = (Zlength (f)))) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (f)))) (PreH3 : ((Zlength (f)) <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH7 : (n_pre = (Zlength (f)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |->_)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (PreH1 : (2 <= (Zlength (f)))) (PreH2 : ((Zlength (f)) <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH6 : (n_pre = (Zlength (f)))) ,
  ((( &( "gain" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (PreH1 : (2 <= (Zlength (f)))) (PreH2 : ((Zlength (f)) <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH6 : (n_pre = (Zlength (f)))) ,
  ((( &( "gain" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |-> 1)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ ((n_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition solver_safety_wit_10 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |-> 1)
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_11 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |-> (-1))
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ ((n_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition solver_safety_wit_12 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "sum" ) )) # Int  |-> (-1))
  **  (IntArray.undef_full retval (n_pre - 1 ) )
  **  ((( &( "gain" ) )) # Ptr  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_13 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((-1) <= i)) (PreH8 : (i <= (n_pre - 2 ))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH12 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.undef_seg gain 0 (i + 1 ) )
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ ((sum + (-1) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (-1) )) ”
.

Definition solver_safety_wit_15 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ ((sum + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((-n_pre) <= sum)) (PreH11 : (sum <= n_pre)) (PreH12 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH13 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_17 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_19 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_20 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_21 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (-1) ))
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_22 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 canonical_gains 0)) /\ ((Znth j_2 canonical_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (GainBuildState f 0 canonical_gains sum )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) canonical_gains )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 canonical_gains 0)) /\ ((Znth j_2 canonical_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (GainBuildState f 0 canonical_gains sum )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) canonical_gains )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (sorted_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains )) ,
  ((( &( "cur" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (sorted_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int64  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_26 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (sorted_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int64  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (sorted_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "ans" ) )) # Int  |-> (-1))
  **  ((( &( "cur" ) )) # Int64  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (ans = (-1))) (PreH10 : ((-n_pre) <= sum)) (PreH11 : (sum <= n_pre)) (PreH12 : ((-40000000000) <= cur)) (PreH13 : (cur <= 40000000000)) (PreH14 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH16 : (PreparedGains f sorted_gains )) (PreH17 : (GainSearchState k_pre sorted_gains i cur )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre - 1 ))) (PreH9 : (ans = (-1))) (PreH10 : ((-n_pre) <= sum)) (PreH11 : (sum <= n_pre)) (PreH12 : ((-40000000000) <= cur)) (PreH13 : (cur <= 40000000000)) (PreH14 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH15 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH16 : (PreparedGains f sorted_gains )) (PreH17 : (GainSearchState k_pre sorted_gains i cur )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (ans = (-1))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((-40000000000) <= cur)) (PreH14 : (cur <= 40000000000)) (PreH15 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH17 : (PreparedGains f sorted_gains )) (PreH18 : (GainSearchState k_pre sorted_gains i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "cur" ) )) # Int64  |-> cur)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
|--
  “ ((cur + (Znth i sorted_gains 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (cur + (Znth i sorted_gains 0) )) ”
.

Definition solver_safety_wit_31 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains 0) ) >= k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains )) (PreH19 : (GainSearchState k_pre sorted_gains i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "cur" ) )) # Int64  |-> (cur + (Znth i sorted_gains 0) ))
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_32 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains 0) ) >= k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains )) (PreH19 : (GainSearchState k_pre sorted_gains i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "cur" ) )) # Int64  |-> (cur + (Znth i sorted_gains 0) ))
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_33 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains 0) ) < k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains )) (PreH19 : (GainSearchState k_pre sorted_gains i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "cur" ) )) # Int64  |-> (cur + (Znth i sorted_gains 0) ))
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1_1 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full retval (n_pre - 1 ) )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (n_pre - 2 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((n_pre - 2 ) + 1 ) built_gains 1 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg retval 0 ((n_pre - 2 ) + 1 ) )
  **  (IntArray.seg retval ((n_pre - 2 ) + 1 ) (n_pre - 1 ) built_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  (IntArray.undef_full retval (n_pre - 1 ) )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (n_pre - 2 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((n_pre - 2 ) + 1 ) built_gains 1 ) ”
  &&  (IntArray.undef_seg retval 0 ((n_pre - 2 ) + 1 ) )
  **  (IntArray.seg retval ((n_pre - 2 ) + 1 ) (n_pre - 1 ) built_gains )
).

Definition solver_entail_wit_1_2 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full retval (n_pre - 1 ) )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= (-1)) ” 
  &&  “ ((-1) <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (n_pre - 2 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((n_pre - 2 ) + 1 ) built_gains (-1) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg retval 0 ((n_pre - 2 ) + 1 ) )
  **  (IntArray.seg retval ((n_pre - 2 ) + 1 ) (n_pre - 1 ) built_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : ((Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (retval <> 0)) (PreH3 : (2 <= (Zlength (f)))) (PreH4 : ((Zlength (f)) <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH8 : (n_pre = (Zlength (f)))) ,
  (IntArray.undef_full retval (n_pre - 1 ) )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= (-1)) ” 
  &&  “ ((-1) <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (n_pre - 2 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((n_pre - 2 ) + 1 ) built_gains (-1) ) ”
  &&  (IntArray.undef_seg retval 0 ((n_pre - 2 ) + 1 ) )
  **  (IntArray.seg retval ((n_pre - 2 ) + 1 ) (n_pre - 1 ) built_gains )
).

Definition solver_entail_wit_2_1 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains_2: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains_2)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains_2 sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains_2 )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= (sum + 1 )) ” 
  &&  “ ((sum + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (i - 1 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((i - 1 ) + 1 ) built_gains (sum + 1 ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 ((i - 1 ) + 1 ) )
  **  (IntArray.seg gain ((i - 1 ) + 1 ) (n_pre - 1 ) built_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (gain: Z) (built_gains_2: (@list Z)) (sum: Z) (i: Z) (PreH1 : (sum <= INT_MAX)) (PreH2 : (sum >= INT_MIN)) (PreH3 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) = 49)) (PreH4 : (i >= 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (f)) = n_pre)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH11 : ((-1) <= i)) (PreH12 : (i <= (n_pre - 2 ))) (PreH13 : ((-n_pre) <= sum)) (PreH14 : (sum <= n_pre)) (PreH15 : ((Zlength (built_gains_2)) = ((n_pre - i ) - 2 ))) (PreH16 : (GainBuildState f (i + 1 ) built_gains_2 sum )) ,
  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains_2 )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= (sum + 1 )) ” 
  &&  “ ((sum + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (i - 1 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((i - 1 ) + 1 ) built_gains (sum + 1 ) ) ”
  &&  (IntArray.seg gain ((i - 1 ) + 1 ) (n_pre - 1 ) built_gains )
).

Definition solver_entail_wit_2_2 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains_2: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH2 : (i >= 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((Zlength (built_gains_2)) = ((n_pre - i ) - 2 ))) (PreH14 : (GainBuildState f (i + 1 ) built_gains_2 sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains_2 )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= (sum + (-1) )) ” 
  &&  “ ((sum + (-1) ) <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (i - 1 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((i - 1 ) + 1 ) built_gains (sum + (-1) ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 ((i - 1 ) + 1 ) )
  **  (IntArray.seg gain ((i - 1 ) + 1 ) (n_pre - 1 ) built_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (gain: Z) (built_gains_2: (@list Z)) (sum: Z) (i: Z) (PreH1 : (sum <= INT_MAX)) (PreH2 : (sum >= INT_MIN)) (PreH3 : ((Znth i (app (f) ((cons (0) ((@nil Z))))) 0) <> 49)) (PreH4 : (i >= 0)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (1 <= k_pre)) (PreH8 : (k_pre <= 1000000000)) (PreH9 : ((Zlength (f)) = n_pre)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH11 : ((-1) <= i)) (PreH12 : (i <= (n_pre - 2 ))) (PreH13 : ((-n_pre) <= sum)) (PreH14 : (sum <= n_pre)) (PreH15 : ((Zlength (built_gains_2)) = ((n_pre - i ) - 2 ))) (PreH16 : (GainBuildState f (i + 1 ) built_gains_2 sum )) ,
  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains_2 )
|--
  EX (built_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= (sum + (-1) )) ” 
  &&  “ ((sum + (-1) ) <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - (i - 1 ) ) - 2 )) ” 
  &&  “ (GainBuildState f ((i - 1 ) + 1 ) built_gains (sum + (-1) ) ) ”
  &&  (IntArray.seg gain ((i - 1 ) + 1 ) (n_pre - 1 ) built_gains )
).

Definition solver_entail_wit_3 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((-n_pre) <= sum)) (PreH11 : (sum <= n_pre)) (PreH12 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH13 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 (i + 1 ) )
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  EX (canonical_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((Zlength (canonical_gains)) = (n_pre - 1 )) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 canonical_gains 0)) /\ ((Znth j_2 canonical_gains 0) <= n_pre))) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ (GainBuildState f 0 canonical_gains sum ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) canonical_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((-n_pre) <= sum)) (PreH11 : (sum <= n_pre)) (PreH12 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH13 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  EX (canonical_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((Zlength (canonical_gains)) = (n_pre - 1 )) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 canonical_gains 0)) /\ ((Znth j_2 canonical_gains 0) <= n_pre))) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ (GainBuildState f 0 canonical_gains sum ) ”
  &&  (IntArray.full gain (n_pre - 1 ) canonical_gains )
).

Definition solver_entail_wit_4 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (gain: Z) (sorted: (@list Z)) (PreH1 : (Permutation canonical_gains sorted )) (PreH2 : (decreasing sorted )) (PreH3 : ((Zlength (sorted)) = (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (f)) = n_pre)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH10 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH11 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 canonical_gains 0)) /\ ((Znth j_4 canonical_gains 0) <= n_pre)))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : (GainBuildState f 0 canonical_gains sum )) ,
  (IntArray.full gain (n_pre - 1 ) sorted )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  EX (sorted_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((Zlength (sorted_gains)) = (n_pre - 1 )) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre))) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ (PreparedGains f sorted_gains ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (sorted: (@list Z)) (PreH1 : (Permutation canonical_gains sorted )) (PreH2 : (decreasing sorted )) (PreH3 : ((Zlength (sorted)) = (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (f)) = n_pre)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH10 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH11 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 canonical_gains 0)) /\ ((Znth j_4 canonical_gains 0) <= n_pre)))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : (GainBuildState f 0 canonical_gains sum )) ,
  TT && emp 
|--
  “ (PreparedGains f sorted ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= n_pre))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (sorted: (@list Z)) (PreH1 : (Permutation canonical_gains sorted )) (PreH2 : (decreasing sorted )) (PreH3 : ((Zlength (sorted)) = (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (f)) = n_pre)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH10 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH11 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 canonical_gains 0)) /\ ((Znth j_4 canonical_gains 0) <= n_pre)))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : (GainBuildState f 0 canonical_gains sum )) ,
  (PreparedGains f sorted )
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (sorted: (@list Z)) (PreH1 : (Permutation canonical_gains sorted )) (PreH2 : (decreasing sorted )) (PreH3 : ((Zlength (sorted)) = (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (f)) = n_pre)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH10 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH11 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 canonical_gains 0)) /\ ((Znth j_4 canonical_gains 0) <= n_pre)))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : (GainBuildState f 0 canonical_gains sum )) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted 0)) /\ ((Znth j_2 sorted 0) <= n_pre)))
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (sorted: (@list Z)) (PreH1 : (Permutation canonical_gains sorted )) (PreH2 : (decreasing sorted )) (PreH3 : ((Zlength (sorted)) = (n_pre - 1 ))) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 1000000000)) (PreH8 : ((Zlength (f)) = n_pre)) (PreH9 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH10 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH11 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 canonical_gains 0)) /\ ((Znth j_4 canonical_gains 0) <= n_pre)))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : (GainBuildState f 0 canonical_gains sum )) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))
.

Definition solver_entail_wit_5 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 sorted_gains_2 0)) /\ ((Znth j_4 sorted_gains_2 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains_2 )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains_2 )
|--
  EX (sorted_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= 0) ” 
  &&  “ (0 <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains)) = (n_pre - 1 )) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre))) ” 
  &&  “ (PreparedGains f sorted_gains ) ” 
  &&  “ (GainSearchState k_pre sorted_gains 0 0 ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (sum: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 sorted_gains_2 0)) /\ ((Znth j_4 sorted_gains_2 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains_2 )) ,
  TT && emp 
|--
  “ (GainSearchState k_pre sorted_gains_2 0 0 ) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains_2 0)) /\ ((Znth j_2 sorted_gains_2 0) <= n_pre))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (sum: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 sorted_gains_2 0)) /\ ((Znth j_4 sorted_gains_2 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains_2 )) ,
  (GainSearchState k_pre sorted_gains_2 0 0 )
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (sum: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 sorted_gains_2 0)) /\ ((Znth j_4 sorted_gains_2 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains_2 )) ,
  forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains_2 0)) /\ ((Znth j_2 sorted_gains_2 0) <= n_pre)))
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (sum: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < n_pre)) -> (((Znth j_3 f 0) = 48) \/ ((Znth j_3 f 0) = 49)))) (PreH7 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH8 : forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_4 sorted_gains_2 0)) /\ ((Znth j_4 sorted_gains_2 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (PreparedGains f sorted_gains_2 )) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))
.

Definition solver_entail_wit_6 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains_2: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains_2 0) ) < k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains_2 0)) /\ ((Znth j_2 sorted_gains_2 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains_2 )) (PreH19 : (GainSearchState k_pre sorted_gains_2 i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains_2 )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  EX (sorted_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (ans = (-1)) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= (cur + (Znth i sorted_gains_2 0) )) ” 
  &&  “ ((cur + (Znth i sorted_gains_2 0) ) <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains)) = (n_pre - 1 )) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre))) ” 
  &&  “ (PreparedGains f sorted_gains ) ” 
  &&  “ (GainSearchState k_pre sorted_gains (i + 1 ) (cur + (Znth i sorted_gains_2 0) ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains_2 0) ) < k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains_2 0)) /\ ((Znth j_2 sorted_gains_2 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains_2 )) (PreH19 : (GainSearchState k_pre sorted_gains_2 i cur )) ,
  TT && emp 
|--
  “ (GainSearchState k_pre sorted_gains_2 (i + 1 ) (cur + (Znth i sorted_gains_2 0) ) ) ” 
  &&  “ ((-40000000000) <= (cur + (Znth i sorted_gains_2 0) )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains_2 0) ) < k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains_2 0)) /\ ((Znth j_2 sorted_gains_2 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains_2 )) (PreH19 : (GainSearchState k_pre sorted_gains_2 i cur )) ,
  (GainSearchState k_pre sorted_gains_2 (i + 1 ) (cur + (Znth i sorted_gains_2 0) ) )
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (sorted_gains_2: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains_2 0) ) < k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH17 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains_2 0)) /\ ((Znth j_2 sorted_gains_2 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains_2 )) (PreH19 : (GainSearchState k_pre sorted_gains_2 i cur )) ,
  ((-40000000000) <= (cur + (Znth i sorted_gains_2 0) ))
.

Definition solver_entail_wit_7_1 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains_2: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 f 0) = 48) \/ ((Znth j_2 f 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (ans = (-1))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((-40000000000) <= cur)) (PreH14 : (cur <= 40000000000)) (PreH15 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_3 sorted_gains_2 0)) /\ ((Znth j_3 sorted_gains_2 0) <= n_pre)))) (PreH17 : (PreparedGains f sorted_gains_2 )) (PreH18 : (GainSearchState k_pre sorted_gains_2 i cur )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains_2 )
|--
  EX (sorted_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= cur) ” 
  &&  “ (cur <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains)) = (n_pre - 1 )) ” 
  &&  “ (PreparedGains f sorted_gains ) ” 
  &&  “ (FishingSearchResult k_pre f sorted_gains ans ) ” 
  &&  “ (Spec k_pre f ans ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (Zlength (sorted_gains)) sorted_gains )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains_2: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 f 0) = 48) \/ ((Znth j_2 f 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (ans = (-1))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((-40000000000) <= cur)) (PreH14 : (cur <= 40000000000)) (PreH15 : ((Zlength (sorted_gains_2)) = (n_pre - 1 ))) (PreH16 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_3 sorted_gains_2 0)) /\ ((Znth j_3 sorted_gains_2 0) <= n_pre)))) (PreH17 : (PreparedGains f sorted_gains_2 )) (PreH18 : (GainSearchState k_pre sorted_gains_2 i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains_2 )
|--
  EX (sorted_gains: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= cur) ” 
  &&  “ (cur <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains)) = (n_pre - 1 )) ” 
  &&  “ (PreparedGains f sorted_gains ) ” 
  &&  “ (FishingSearchResult k_pre f sorted_gains ans ) ” 
  &&  “ (Spec k_pre f ans ) ”
  &&  (IntArray.full gain (Zlength (sorted_gains)) sorted_gains )
).

Definition solver_entail_wit_7_2 := 
(
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains 0) ) >= k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 f 0) = 48) \/ ((Znth j_2 f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH17 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_3 sorted_gains 0)) /\ ((Znth j_3 sorted_gains 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains )) (PreH19 : (GainSearchState k_pre sorted_gains i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  EX (sorted_gains_2: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (i + 2 )) ” 
  &&  “ ((i + 2 ) <= n_pre) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= (cur + (Znth i sorted_gains 0) )) ” 
  &&  “ ((cur + (Znth i sorted_gains 0) ) <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains_2)) = (n_pre - 1 )) ” 
  &&  “ (PreparedGains f sorted_gains_2 ) ” 
  &&  “ (FishingSearchResult k_pre f sorted_gains_2 (i + 2 ) ) ” 
  &&  “ (Spec k_pre f (i + 2 ) ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (Zlength (sorted_gains_2)) sorted_gains_2 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : ((cur + (Znth i sorted_gains 0) ) >= k_pre)) (PreH2 : (i < (n_pre - 1 ))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((Zlength (f)) = n_pre)) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 f 0) = 48) \/ ((Znth j_2 f 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i <= (n_pre - 1 ))) (PreH11 : (ans = (-1))) (PreH12 : ((-n_pre) <= sum)) (PreH13 : (sum <= n_pre)) (PreH14 : ((-40000000000) <= cur)) (PreH15 : (cur <= 40000000000)) (PreH16 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH17 : forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_3 sorted_gains 0)) /\ ((Znth j_3 sorted_gains 0) <= n_pre)))) (PreH18 : (PreparedGains f sorted_gains )) (PreH19 : (GainSearchState k_pre sorted_gains i cur )) ,
  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  EX (sorted_gains_2: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= (i + 2 )) ” 
  &&  “ ((i + 2 ) <= n_pre) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= (cur + (Znth i sorted_gains 0) )) ” 
  &&  “ ((cur + (Znth i sorted_gains 0) ) <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains_2)) = (n_pre - 1 )) ” 
  &&  “ (PreparedGains f sorted_gains_2 ) ” 
  &&  “ (FishingSearchResult k_pre f sorted_gains_2 (i + 2 ) ) ” 
  &&  “ (Spec k_pre f (i + 2 ) ) ”
  &&  (IntArray.full gain (Zlength (sorted_gains_2)) sorted_gains_2 )
).

Definition solver_return_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (ans: Z) (sum: Z) (cur: Z) (sorted_gains: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((-1) <= ans)) (PreH8 : (ans <= n_pre)) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : ((-40000000000) <= cur)) (PreH12 : (cur <= 40000000000)) (PreH13 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH14 : (PreparedGains f sorted_gains )) (PreH15 : (FishingSearchResult k_pre f sorted_gains ans )) (PreH16 : (Spec k_pre f ans )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ (Spec k_pre f ans ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_1 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (2 <= (Zlength (f)))) (PreH3 : ((Zlength (f)) <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH7 : (n_pre = (Zlength (f)))) ,
  (IntArray.undef_full retval (n_pre - 1 ) )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ (retval <> 0) ” 
  &&  “ (2 <= (Zlength (f))) ” 
  &&  “ ((Zlength (f)) <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49))) ” 
  &&  “ (n_pre = (Zlength (f))) ”
  &&  (((s_pre + ((n_pre - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (n_pre - 1 ) (app (f) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre (n_pre - 1 ) 0 (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_full retval (n_pre - 1 ) )
.

Definition solver_partial_solve_wit_2_pure := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (PreH1 : (2 <= (Zlength (f)))) (PreH2 : ((Zlength (f)) <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH6 : (n_pre = (Zlength (f)))) ,
  ((( &( "gain" ) )) # Ptr  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (((n_pre - 1 ) * sizeof(INT) ) = ((n_pre - 1 ) * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (PreH1 : (2 <= (Zlength (f)))) (PreH2 : ((Zlength (f)) <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49)))) (PreH6 : (n_pre = (Zlength (f)))) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
|--
  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (((n_pre - 1 ) * sizeof(INT) ) = ((n_pre - 1 ) * sizeof(INT) )) ” 
  &&  “ (2 <= (Zlength (f))) ” 
  &&  “ ((Zlength (f)) <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (f)))) -> (((Znth i f 0) = 48) \/ ((Znth i f 0) = 49))) ” 
  &&  “ (n_pre = (Zlength (f))) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((-n_pre) <= sum)) (PreH11 : (sum <= n_pre)) (PreH12 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH13 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 (i + 1 ) )
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - i ) - 2 )) ” 
  &&  “ (GainBuildState f (i + 1 ) built_gains sum ) ”
  &&  (((gain + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i gain i 0 (i + 1 ) )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
.

Definition solver_partial_solve_wit_4 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (built_gains: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((-n_pre) <= sum)) (PreH11 : (sum <= n_pre)) (PreH12 : ((Zlength (built_gains)) = ((n_pre - i ) - 2 ))) (PreH13 : (GainBuildState f (i + 1 ) built_gains sum )) ,
  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
|--
  “ (i >= 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((Zlength (built_gains)) = ((n_pre - i ) - 2 )) ” 
  &&  “ (GainBuildState f (i + 1 ) built_gains sum ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (f) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg gain 0 i )
  **  (((gain + (i * sizeof(INT)))) # Int  |-> sum)
  **  (IntArray.seg gain (i + 1 ) (n_pre - 1 ) built_gains )
.

Definition solver_partial_solve_wit_5_pure := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 canonical_gains 0)) /\ ((Znth j_2 canonical_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (GainBuildState f 0 canonical_gains sum )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  ((( &( "gain" ) )) # Ptr  |-> gain)
  **  (IntArray.full gain (n_pre - 1 ) canonical_gains )
|--
  “ ((n_pre - 1 ) = (Zlength (canonical_gains))) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ”
.

Definition solver_partial_solve_wit_5_aux := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (canonical_gains: (@list Z)) (sum: Z) (gain: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((Zlength (canonical_gains)) = (n_pre - 1 ))) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 canonical_gains 0)) /\ ((Znth j_2 canonical_gains 0) <= n_pre)))) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : (GainBuildState f 0 canonical_gains sum )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) canonical_gains )
|--
  “ ((n_pre - 1 ) = (Zlength (canonical_gains))) ” 
  &&  “ (sizeof(INT) = sizeof(INT)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((Zlength (canonical_gains)) = (n_pre - 1 )) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 canonical_gains 0)) /\ ((Znth j_2 canonical_gains 0) <= n_pre))) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ (GainBuildState f 0 canonical_gains sum ) ”
  &&  (IntArray.full gain (n_pre - 1 ) canonical_gains )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Definition solver_partial_solve_wit_6 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (gain: Z) (sorted_gains: (@list Z)) (cur: Z) (sum: Z) (ans: Z) (i: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((Zlength (f)) = n_pre)) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 1 ))) (PreH10 : (ans = (-1))) (PreH11 : ((-n_pre) <= sum)) (PreH12 : (sum <= n_pre)) (PreH13 : ((-40000000000) <= cur)) (PreH14 : (cur <= 40000000000)) (PreH15 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre)))) (PreH17 : (PreparedGains f sorted_gains )) (PreH18 : (GainSearchState k_pre sorted_gains i cur )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (n_pre - 1 ) sorted_gains )
|--
  “ (i < (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 1 )) ” 
  &&  “ (ans = (-1)) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= cur) ” 
  &&  “ (cur <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains)) = (n_pre - 1 )) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (n_pre - 1 ))) -> (((-n_pre) <= (Znth j_2 sorted_gains 0)) /\ ((Znth j_2 sorted_gains 0) <= n_pre))) ” 
  &&  “ (PreparedGains f sorted_gains ) ” 
  &&  “ (GainSearchState k_pre sorted_gains i cur ) ”
  &&  (((gain + (i * sizeof(INT)))) # Int  |-> (Znth i sorted_gains 0))
  **  (IntArray.missing_i gain i 0 (n_pre - 1 ) sorted_gains )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
.

Definition solver_partial_solve_wit_7 := 
forall (k_pre: Z) (n_pre: Z) (s_pre: Z) (f: (@list Z)) (ans: Z) (sum: Z) (cur: Z) (gain: Z) (sorted_gains: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : ((Zlength (f)) = n_pre)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49)))) (PreH7 : ((-1) <= ans)) (PreH8 : (ans <= n_pre)) (PreH9 : ((-n_pre) <= sum)) (PreH10 : (sum <= n_pre)) (PreH11 : ((-40000000000) <= cur)) (PreH12 : (cur <= 40000000000)) (PreH13 : ((Zlength (sorted_gains)) = (n_pre - 1 ))) (PreH14 : (PreparedGains f sorted_gains )) (PreH15 : (FishingSearchResult k_pre f sorted_gains ans )) (PreH16 : (Spec k_pre f ans )) ,
  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full gain (Zlength (sorted_gains)) sorted_gains )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((Zlength (f)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j f 0) = 48) \/ ((Znth j f 0) = 49))) ” 
  &&  “ ((-1) <= ans) ” 
  &&  “ (ans <= n_pre) ” 
  &&  “ ((-n_pre) <= sum) ” 
  &&  “ (sum <= n_pre) ” 
  &&  “ ((-40000000000) <= cur) ” 
  &&  “ (cur <= 40000000000) ” 
  &&  “ ((Zlength (sorted_gains)) = (n_pre - 1 )) ” 
  &&  “ (PreparedGains f sorted_gains ) ” 
  &&  “ (FishingSearchResult k_pre f sorted_gains ans ) ” 
  &&  “ (Spec k_pre f ans ) ”
  &&  (IntArray.full gain (Zlength (sorted_gains)) sorted_gains )
  **  (CharArray.full s_pre (n_pre + 1 ) (app (f) ((cons (0) ((@nil Z))))) )
.

Module Type VC_Correct.


Axiom proof_of_cmp_desc_safety_wit_1 : cmp_desc_safety_wit_1.
Axiom proof_of_cmp_desc_safety_wit_2 : cmp_desc_safety_wit_2.
Axiom proof_of_cmp_desc_safety_wit_3 : cmp_desc_safety_wit_3.
Axiom proof_of_cmp_desc_safety_wit_4 : cmp_desc_safety_wit_4.
Axiom proof_of_cmp_desc_return_wit_1 : cmp_desc_return_wit_1.
Axiom proof_of_cmp_desc_return_wit_2 : cmp_desc_return_wit_2.
Axiom proof_of_cmp_desc_return_wit_3 : cmp_desc_return_wit_3.
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
Axiom proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1.
Axiom proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
