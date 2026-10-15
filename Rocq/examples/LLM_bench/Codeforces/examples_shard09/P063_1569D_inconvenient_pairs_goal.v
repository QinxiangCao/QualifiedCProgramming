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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P063_1569D_inconvenient_pairs_lib.
Require Import AUXLib.MonotonicList.
Local Open Scope sac.

(*----- Function strip -----*)

Definition strip_safety_wit_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (streets)) = n_pre)) (PreH4 : (mono_inc streets )) (PreH5 : ((Znth 0 streets 0) = 0)) (PreH6 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= 1000000)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition strip_safety_wit_2 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (streets)) = n_pre)) (PreH4 : (mono_inc streets )) (PreH5 : ((Znth 0 streets 0) = 0)) (PreH6 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= 1000000)) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_3 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (streets)) = n_pre)) (PreH4 : (mono_inc streets )) (PreH5 : ((Znth 0 streets 0) = 0)) (PreH6 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= 1000000)) ,
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition strip_safety_wit_4 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition strip_safety_wit_4_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition strip_safety_wit_4_split_goal_2 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition strip_safety_wit_5 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((((hi - lo ) + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition strip_safety_wit_6 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (((hi - lo ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((hi - lo ) + 1 )) ”
.

Definition strip_safety_wit_7 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((hi - lo ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hi - lo )) ”
.

Definition strip_safety_wit_8 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_9 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition strip_safety_wit_10 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition strip_safety_wit_10_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition strip_safety_wit_10_split_goal_2 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition strip_safety_wit_11 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((((hi - lo ) + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition strip_safety_wit_12 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (((hi - lo ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((hi - lo ) + 1 )) ”
.

Definition strip_safety_wit_13 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((hi - lo ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hi - lo )) ”
.

Definition strip_safety_wit_14 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_15 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition strip_safety_wit_16 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
) \/
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
).

Definition strip_safety_wit_16_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition strip_safety_wit_16_split_goal_2 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((INT_MIN) <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ”
.

Definition strip_safety_wit_17 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((((hi - lo ) + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition strip_safety_wit_18 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (((hi - lo ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((hi - lo ) + 1 )) ”
.

Definition strip_safety_wit_19 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ ((hi - lo ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (hi - lo )) ”
.

Definition strip_safety_wit_20 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_21 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition strip_safety_wit_22 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition strip_safety_wit_23 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_24 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition strip_safety_wit_25 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_26 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ”
.

Definition strip_safety_wit_27 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_28 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition strip_safety_wit_29 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition strip_safety_wit_30 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition strip_safety_wit_31 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_32 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_safety_wit_33 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition strip_entail_wit_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((Zlength (streets)) = n_pre)) (PreH4 : (mono_inc streets )) (PreH5 : ((Znth 0 streets 0) = 0)) (PreH6 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH7 : (0 <= v_pre)) (PreH8 : (v_pre <= 1000000)) ,
  (IntArray.full s_pre n_pre streets )
|--
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Znth 0 streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth (n_pre - 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Znth 0 streets 0) <= v_pre) ” 
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Znth 0 streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth ((n_pre - 1 ) + 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_2_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo < hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets )
|--
  (“ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi <= INT_MAX) ” 
  &&  “ (lo <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi >= INT_MIN) ” 
  &&  “ (lo >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo < hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets ))
  ||
  (EX (hi_2: Z)  (lo_2: Z) ,
  “ (0 <= (lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi_2 <= INT_MAX) ” 
  &&  “ (lo_2 <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi_2 >= INT_MIN) ” 
  &&  “ (lo_2 >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo_2 < hi_2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo_2) ” 
  &&  “ (lo_2 <= hi_2) ” 
  &&  “ (hi_2 < n_pre) ” 
  &&  “ ((Znth lo_2 streets 0) <= v_pre) ” 
  &&  “ (hi_2 = (n_pre - 1 )) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_2)
  **  ((( &( "hi" ) )) # Int  |-> hi_2)
  **  (IntArray.full s_pre n_pre streets ))
  ||
  (EX (hi_3: Z)  (lo_3: Z) ,
  “ (0 <= (lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi_3 <= INT_MAX) ” 
  &&  “ (lo_3 <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi_3 >= INT_MIN) ” 
  &&  “ (lo_3 >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo_3 < hi_3) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo_3) ” 
  &&  “ (lo_3 <= hi_3) ” 
  &&  “ (hi_3 < n_pre) ” 
  &&  “ ((Znth lo_3 streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi_3 + 1 ) streets 0)) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_3)
  **  ((( &( "hi" ) )) # Int  |-> hi_3)
  **  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_2_2 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi_2: Z) (lo_2: Z) (PreH1 : (lo_2 < hi_2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo_2)) (PreH11 : (lo_2 <= hi_2)) (PreH12 : (hi_2 < n_pre)) (PreH13 : ((Znth lo_2 streets 0) <= v_pre)) (PreH14 : (hi_2 = (n_pre - 1 ))) ,
  ((( &( "mid" ) )) # Int  |-> (lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_2)
  **  ((( &( "hi" ) )) # Int  |-> hi_2)
  **  (IntArray.full s_pre n_pre streets )
|--
  (EX (hi: Z)  (lo: Z) ,
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi <= INT_MAX) ” 
  &&  “ (lo <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi >= INT_MIN) ” 
  &&  “ (lo >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo < hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (0 <= (lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi_2 <= INT_MAX) ” 
  &&  “ (lo_2 <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi_2 >= INT_MIN) ” 
  &&  “ (lo_2 >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo_2 < hi_2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo_2) ” 
  &&  “ (lo_2 <= hi_2) ” 
  &&  “ (hi_2 < n_pre) ” 
  &&  “ ((Znth lo_2 streets 0) <= v_pre) ” 
  &&  “ (hi_2 = (n_pre - 1 )) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_2)
  **  ((( &( "hi" ) )) # Int  |-> hi_2)
  **  (IntArray.full s_pre n_pre streets ))
  ||
  (EX (hi_3: Z)  (lo_3: Z) ,
  “ (0 <= (lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi_3 <= INT_MAX) ” 
  &&  “ (lo_3 <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi_3 >= INT_MIN) ” 
  &&  “ (lo_3 >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo_3 < hi_3) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo_3) ” 
  &&  “ (lo_3 <= hi_3) ” 
  &&  “ (hi_3 < n_pre) ” 
  &&  “ ((Znth lo_3 streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi_3 + 1 ) streets 0)) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_3)
  **  ((( &( "hi" ) )) # Int  |-> hi_3)
  **  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_2_3 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi_3: Z) (lo_3: Z) (PreH1 : (lo_3 < hi_3)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo_3)) (PreH11 : (lo_3 <= hi_3)) (PreH12 : (hi_3 < n_pre)) (PreH13 : ((Znth lo_3 streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi_3 + 1 ) streets 0))) ,
  ((( &( "mid" ) )) # Int  |-> (lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_3)
  **  ((( &( "hi" ) )) # Int  |-> hi_3)
  **  (IntArray.full s_pre n_pre streets )
|--
  (EX (hi: Z)  (lo: Z) ,
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi <= INT_MAX) ” 
  &&  “ (lo <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi >= INT_MIN) ” 
  &&  “ (lo >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo < hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo)
  **  ((( &( "hi" ) )) # Int  |-> hi)
  **  (IntArray.full s_pre n_pre streets ))
  ||
  (EX (hi_2: Z)  (lo_2: Z) ,
  “ (0 <= (lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi_2 <= INT_MAX) ” 
  &&  “ (lo_2 <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi_2 >= INT_MIN) ” 
  &&  “ (lo_2 >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo_2 < hi_2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo_2) ” 
  &&  “ (lo_2 <= hi_2) ” 
  &&  “ (hi_2 < n_pre) ” 
  &&  “ ((Znth lo_2 streets 0) <= v_pre) ” 
  &&  “ (hi_2 = (n_pre - 1 )) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo_2 + (((hi_2 - lo_2 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_2)
  **  ((( &( "hi" ) )) # Int  |-> hi_2)
  **  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (0 <= (lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi_3 <= INT_MAX) ” 
  &&  “ (lo_3 <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi_3 >= INT_MIN) ” 
  &&  “ (lo_3 >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo_3 < hi_3) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo_3) ” 
  &&  “ (lo_3 <= hi_3) ” 
  &&  “ (hi_3 < n_pre) ” 
  &&  “ ((Znth lo_3 streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi_3 + 1 ) streets 0)) ”
  &&  ((( &( "mid" ) )) # Int  |-> (lo_3 + (((hi_3 - lo_3 ) + 1 ) ÷ 2 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "v" ) )) # Int  |-> v_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_3)
  **  ((( &( "hi" ) )) # Int  |-> hi_3)
  **  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_3_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (hi = (n_pre - 1 )) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi + 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_3_2 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
|--
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (hi = (n_pre - 1 )) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi + 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_3_3 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (hi = (n_pre - 1 )) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi + 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_3_4 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) + 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_3_5 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
|--
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) + 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
.

Definition strip_entail_wit_3_6 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0) > v_pre)) (PreH2 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH3 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH4 : (hi <= INT_MAX)) (PreH5 : (lo <= INT_MAX)) (PreH6 : (v_pre <= INT_MAX)) (PreH7 : (hi >= INT_MIN)) (PreH8 : (lo >= INT_MIN)) (PreH9 : (v_pre >= INT_MIN)) (PreH10 : (lo < hi)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : ((Zlength (streets)) = n_pre)) (PreH14 : (mono_inc streets )) (PreH15 : ((Znth 0 streets 0) = 0)) (PreH16 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH17 : (0 <= v_pre)) (PreH18 : (v_pre <= 1000000)) (PreH19 : (0 <= lo)) (PreH20 : (lo <= hi)) (PreH21 : (hi < n_pre)) (PreH22 : ((Znth lo streets 0) <= v_pre)) (PreH23 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
  ||
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 )) ” 
  &&  “ (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) - 1 ) + 1 ) streets 0)) ”
  &&  (IntArray.full s_pre n_pre streets ))
.

Definition strip_return_wit_1 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (StripIndex streets v_pre (-1) ) ”
  &&  (IntArray.full s_pre n_pre streets )
) \/
(
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  TT && emp 
|--
  “ (StripIndex streets v_pre (-1) ) ”
  &&  emp
).

Definition strip_return_wit_1_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (StripIndex streets v_pre (-1) )
.

Definition strip_return_wit_2 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (StripIndex streets v_pre (-1) ) ”
  &&  (IntArray.full s_pre n_pre streets )
) \/
(
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  TT && emp 
|--
  “ (StripIndex streets v_pre (-1) ) ”
  &&  emp
).

Definition strip_return_wit_2_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  (StripIndex streets v_pre (-1) )
.

Definition strip_return_wit_3 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (StripIndex streets v_pre (-1) ) ”
  &&  (IntArray.full s_pre n_pre streets )
) \/
(
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  TT && emp 
|--
  “ (StripIndex streets v_pre (-1) ) ”
  &&  emp
).

Definition strip_return_wit_3_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) = v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  (StripIndex streets v_pre (-1) )
.

Definition strip_return_wit_4 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (StripIndex streets v_pre lo ) ”
  &&  (IntArray.full s_pre n_pre streets )
) \/
(
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  TT && emp 
|--
  “ (StripIndex streets v_pre lo ) ”
  &&  emp
).

Definition strip_return_wit_4_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (StripIndex streets v_pre lo )
.

Definition strip_return_wit_5 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (StripIndex streets v_pre lo ) ”
  &&  (IntArray.full s_pre n_pre streets )
) \/
(
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  TT && emp 
|--
  “ (StripIndex streets v_pre lo ) ”
  &&  emp
).

Definition strip_return_wit_5_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (hi = (n_pre - 1 ))) ,
  (StripIndex streets v_pre lo )
.

Definition strip_return_wit_6 := 
(
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (StripIndex streets v_pre lo ) ”
  &&  (IntArray.full s_pre n_pre streets )
) \/
(
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  TT && emp 
|--
  “ (StripIndex streets v_pre lo ) ”
  &&  emp
).

Definition strip_return_wit_6_split_goal_1 := 
forall (v_pre: Z) (n_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : ((Znth lo streets 0) <> v_pre)) (PreH2 : (lo >= hi)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (streets)) = n_pre)) (PreH6 : (mono_inc streets )) (PreH7 : ((Znth 0 streets 0) = 0)) (PreH8 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH9 : (0 <= v_pre)) (PreH10 : (v_pre <= 1000000)) (PreH11 : (0 <= lo)) (PreH12 : (lo <= hi)) (PreH13 : (hi < n_pre)) (PreH14 : ((Znth lo streets 0) <= v_pre)) (PreH15 : (v_pre = (Znth hi streets 0))) ,
  (StripIndex streets v_pre lo )
.

Definition strip_partial_solve_wit_1 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH2 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (lo < hi)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (streets)) = n_pre)) (PreH13 : (mono_inc streets )) (PreH14 : ((Znth 0 streets 0) = 0)) (PreH15 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH16 : (0 <= v_pre)) (PreH17 : (v_pre <= 1000000)) (PreH18 : (0 <= lo)) (PreH19 : (lo <= hi)) (PreH20 : (hi < n_pre)) (PreH21 : ((Znth lo streets 0) <= v_pre)) (PreH22 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi <= INT_MAX) ” 
  &&  “ (lo <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi >= INT_MIN) ” 
  &&  “ (lo >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo < hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  (((s_pre + ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) * sizeof(INT)))) # Int  |-> (Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0))
  **  (IntArray.missing_i s_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) 0 n_pre streets )
.

Definition strip_partial_solve_wit_2 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH2 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (lo < hi)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (streets)) = n_pre)) (PreH13 : (mono_inc streets )) (PreH14 : ((Znth 0 streets 0) = 0)) (PreH15 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH16 : (0 <= v_pre)) (PreH17 : (v_pre <= 1000000)) (PreH18 : (0 <= lo)) (PreH19 : (lo <= hi)) (PreH20 : (hi < n_pre)) (PreH21 : ((Znth lo streets 0) <= v_pre)) (PreH22 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi <= INT_MAX) ” 
  &&  “ (lo <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi >= INT_MIN) ” 
  &&  “ (lo >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo < hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (hi = (n_pre - 1 )) ”
  &&  (((s_pre + ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) * sizeof(INT)))) # Int  |-> (Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0))
  **  (IntArray.missing_i s_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) 0 n_pre streets )
.

Definition strip_partial_solve_wit_3 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) ))) (PreH2 : ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre)) (PreH3 : (hi <= INT_MAX)) (PreH4 : (lo <= INT_MAX)) (PreH5 : (v_pre <= INT_MAX)) (PreH6 : (hi >= INT_MIN)) (PreH7 : (lo >= INT_MIN)) (PreH8 : (v_pre >= INT_MIN)) (PreH9 : (lo < hi)) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre <= 200000)) (PreH12 : ((Zlength (streets)) = n_pre)) (PreH13 : (mono_inc streets )) (PreH14 : ((Znth 0 streets 0) = 0)) (PreH15 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH16 : (0 <= v_pre)) (PreH17 : (v_pre <= 1000000)) (PreH18 : (0 <= lo)) (PreH19 : (lo <= hi)) (PreH20 : (hi < n_pre)) (PreH21 : ((Znth lo streets 0) <= v_pre)) (PreH22 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (0 <= (lo + (((hi - lo ) + 1 ) ÷ 2 ) )) ” 
  &&  “ ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) < n_pre) ” 
  &&  “ (hi <= INT_MAX) ” 
  &&  “ (lo <= INT_MAX) ” 
  &&  “ (v_pre <= INT_MAX) ” 
  &&  “ (hi >= INT_MIN) ” 
  &&  “ (lo >= INT_MIN) ” 
  &&  “ (v_pre >= INT_MIN) ” 
  &&  “ (lo < hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi + 1 ) streets 0)) ”
  &&  (((s_pre + ((lo + (((hi - lo ) + 1 ) ÷ 2 ) ) * sizeof(INT)))) # Int  |-> (Znth (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) streets 0))
  **  (IntArray.missing_i s_pre (lo + (((hi - lo ) + 1 ) ÷ 2 ) ) 0 n_pre streets )
.

Definition strip_partial_solve_wit_4 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre = (Znth hi streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (lo >= hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre = (Znth hi streets 0)) ”
  &&  (((s_pre + (lo * sizeof(INT)))) # Int  |-> (Znth lo streets 0))
  **  (IntArray.missing_i s_pre lo 0 n_pre streets )
.

Definition strip_partial_solve_wit_5 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (hi = (n_pre - 1 ))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (lo >= hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (hi = (n_pre - 1 )) ”
  &&  (((s_pre + (lo * sizeof(INT)))) # Int  |-> (Znth lo streets 0))
  **  (IntArray.missing_i s_pre lo 0 n_pre streets )
.

Definition strip_partial_solve_wit_6 := 
forall (v_pre: Z) (n_pre: Z) (s_pre: Z) (streets: (@list Z)) (hi: Z) (lo: Z) (PreH1 : (lo >= hi)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((Zlength (streets)) = n_pre)) (PreH5 : (mono_inc streets )) (PreH6 : ((Znth 0 streets 0) = 0)) (PreH7 : ((Znth (n_pre - 1 ) streets 0) = 1000000)) (PreH8 : (0 <= v_pre)) (PreH9 : (v_pre <= 1000000)) (PreH10 : (0 <= lo)) (PreH11 : (lo <= hi)) (PreH12 : (hi < n_pre)) (PreH13 : ((Znth lo streets 0) <= v_pre)) (PreH14 : (v_pre < (Znth (hi + 1 ) streets 0))) ,
  (IntArray.full s_pre n_pre streets )
|--
  “ (lo >= hi) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (streets)) = n_pre) ” 
  &&  “ (mono_inc streets ) ” 
  &&  “ ((Znth 0 streets 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) streets 0) = 1000000) ” 
  &&  “ (0 <= v_pre) ” 
  &&  “ (v_pre <= 1000000) ” 
  &&  “ (0 <= lo) ” 
  &&  “ (lo <= hi) ” 
  &&  “ (hi < n_pre) ” 
  &&  “ ((Znth lo streets 0) <= v_pre) ” 
  &&  “ (v_pre < (Znth (hi + 1 ) streets 0)) ”
  &&  (((s_pre + (lo * sizeof(INT)))) # Int  |-> (Znth lo streets 0))
  **  (IntArray.missing_i s_pre lo 0 n_pre streets )
.

(*----- Function item_less -----*)

Definition item_less_return_wit_1 := 
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (grp1_pre < grp2_pre)) ,
  TT && emp 
|--
  (“ (1 <> 0) ” 
  &&  “ (ItemLe4 grp1_pre key1_pre grp2_pre key2_pre ) ” 
  &&  “ (grp1_pre <> grp2_pre) ”
  &&  emp)
  ||
  (“ (1 <> 0) ” 
  &&  “ (ItemLe4 grp1_pre key1_pre grp2_pre key2_pre ) ” 
  &&  “ (key1_pre <> key2_pre) ”
  &&  emp)
.

Definition item_less_return_wit_2 := 
(
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (key1_pre >= key2_pre)) (PreH2 : (grp1_pre = grp2_pre)) (PreH3 : (grp1_pre >= grp2_pre)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (ItemLe4 grp2_pre key2_pre grp1_pre key1_pre ) ”
  &&  emp
) \/
(
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (key1_pre >= key2_pre)) (PreH2 : (grp1_pre = grp2_pre)) (PreH3 : (grp1_pre >= grp2_pre)) ,
  TT && emp 
|--
  “ (ItemLe4 grp2_pre key2_pre grp2_pre key1_pre ) ”
  &&  emp
).

Definition item_less_return_wit_2_split_goal_1 := 
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (key1_pre >= key2_pre)) (PreH2 : (grp1_pre = grp2_pre)) (PreH3 : (grp1_pre >= grp2_pre)) ,
  (ItemLe4 grp2_pre key2_pre grp2_pre key1_pre )
.

Definition item_less_return_wit_3 := 
(
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (key1_pre < key2_pre)) (PreH2 : (grp1_pre = grp2_pre)) (PreH3 : (grp1_pre >= grp2_pre)) ,
  TT && emp 
|--
  “ (1 <> 0) ” 
  &&  “ (ItemLe4 grp1_pre key1_pre grp2_pre key2_pre ) ” 
  &&  “ (key1_pre <> key2_pre) ”
  &&  emp
) \/
(
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (key1_pre < key2_pre)) (PreH2 : (grp1_pre = grp2_pre)) (PreH3 : (grp1_pre >= grp2_pre)) ,
  TT && emp 
|--
  “ (ItemLe4 grp2_pre key1_pre grp2_pre key2_pre ) ”
  &&  emp
).

Definition item_less_return_wit_3_split_goal_1 := 
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (key1_pre < key2_pre)) (PreH2 : (grp1_pre = grp2_pre)) (PreH3 : (grp1_pre >= grp2_pre)) ,
  (ItemLe4 grp2_pre key1_pre grp2_pre key2_pre )
.

Definition item_less_return_wit_4 := 
(
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (grp1_pre <> grp2_pre)) (PreH2 : (grp1_pre >= grp2_pre)) ,
  TT && emp 
|--
  “ (0 = 0) ” 
  &&  “ (ItemLe4 grp2_pre key2_pre grp1_pre key1_pre ) ”
  &&  emp
) \/
(
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (grp1_pre <> grp2_pre)) (PreH2 : (grp1_pre >= grp2_pre)) ,
  TT && emp 
|--
  “ (ItemLe4 grp2_pre key2_pre grp1_pre key1_pre ) ”
  &&  emp
).

Definition item_less_return_wit_4_split_goal_1 := 
forall (key2_pre: Z) (grp2_pre: Z) (key1_pre: Z) (grp1_pre: Z) (PreH1 : (grp1_pre <> grp2_pre)) (PreH2 : (grp1_pre >= grp2_pre)) ,
  (ItemLe4 grp2_pre key2_pre grp1_pre key1_pre )
.

(*----- Function sift_items -----*)

Definition sift_items_safety_wit_1 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation groups keys groups_now keys_now )) (PreH13 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH14 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH16 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * root ) + 1 )) ”
.

Definition sift_items_safety_wit_2 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation groups keys groups_now keys_now )) (PreH13 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH14 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH16 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ ((2 * root ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * root )) ”
.

Definition sift_items_safety_wit_3 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation groups keys groups_now keys_now )) (PreH13 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH14 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH16 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sift_items_safety_wit_4 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= ((2 * root ) + 1 ))) (PreH11 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH12 : (ParallelPermutation groups keys groups_now keys_now )) (PreH13 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH14 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH16 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_items_safety_wit_5 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * root ) + 1 )) ”
.

Definition sift_items_safety_wit_6 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ ((2 * root ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * root )) ”
.

Definition sift_items_safety_wit_7 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sift_items_safety_wit_8 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "child" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_items_safety_wit_9 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_items_safety_wit_10 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) <= upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_items_safety_wit_11 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_items_safety_wit_12 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_items_safety_wit_13 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_items_safety_wit_14 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sift_items_safety_wit_15 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) keys_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ False ”
.

Definition sift_items_safety_wit_16 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) groups_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ False ”
.

Definition sift_items_safety_wit_17 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) )) (PreH4 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH5 : (((2 * root ) + 1 ) <= upper_pre)) (PreH6 : (0 <= upper_pre)) (PreH7 : (upper_pre < n)) (PreH8 : (n <= cap)) (PreH9 : (cap <= 300000)) (PreH10 : ((Zlength (groups_now)) = n)) (PreH11 : ((Zlength (keys_now)) = n)) (PreH12 : (0 <= root_pre)) (PreH13 : (root_pre <= root)) (PreH14 : (root <= upper_pre)) (PreH15 : (0 <= ((2 * root ) + 1 ))) (PreH16 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ False ”
.

Definition sift_items_safety_wit_18 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) keys_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_items_safety_wit_19 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) groups_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "child" ) )) # Int  |-> ((2 * root ) + 1 ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((2 * root ) + 1 ) + 1 )) ”
.

Definition sift_items_safety_wit_20 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth child groups_now 0) (Znth child keys_now 0) (Znth root groups_now 0) (Znth root keys_now 0) )) (PreH4 : (0 <= upper_pre)) (PreH5 : (upper_pre < n)) (PreH6 : (n <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups_now)) = n)) (PreH9 : ((Zlength (keys_now)) = n)) (PreH10 : (0 <= root_pre)) (PreH11 : (root_pre <= root)) (PreH12 : (root <= upper_pre)) (PreH13 : (0 <= child)) (PreH14 : (child <= upper_pre)) (PreH15 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH16 : (ParallelPermutation groups keys groups_now keys_now )) (PreH17 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH18 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH20 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  ((( &( "child" ) )) # Int  |-> child)
|--
  “ False ”
.

Definition sift_items_safety_wit_21 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  ((( &( "child" ) )) # Int  |-> child)
|--
  “ False ”
.

Definition sift_items_safety_wit_22 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  ((( &( "child" ) )) # Int  |-> child)
|--
  “ False ”
.

Definition sift_items_entail_wit_1 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = n)) (PreH6 : ((Zlength (keys)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= upper_pre)) (PreH9 : (HeapOrderedExceptAtFromItems groups keys root_pre upper_pre root_pre )) (PreH10 : (ExtractionFrameItems groups keys (upper_pre + 1 ) )) ,
  (IntArray.full grp_pre n groups )
  **  (IntArray.full key_pre n keys )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root_pre) ” 
  &&  “ (root_pre <= upper_pre) ” 
  &&  “ (0 <= ((2 * root_pre ) + 1 )) ” 
  &&  “ (((2 * root_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root_pre ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root_pre ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = n)) (PreH6 : ((Zlength (keys)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= upper_pre)) (PreH9 : (HeapOrderedExceptAtFromItems groups keys root_pre upper_pre root_pre )) (PreH10 : (ExtractionFrameItems groups keys (upper_pre + 1 ) )) ,
  TT && emp 
|--
  “ (SiftChildrenBelowParentItems groups keys root_pre upper_pre root_pre ) ” 
  &&  “ (ParallelPermutation groups keys groups keys ) ”
  &&  emp
).

Definition sift_items_entail_wit_1_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = n)) (PreH6 : ((Zlength (keys)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= upper_pre)) (PreH9 : (HeapOrderedExceptAtFromItems groups keys root_pre upper_pre root_pre )) (PreH10 : (ExtractionFrameItems groups keys (upper_pre + 1 ) )) ,
  (SiftChildrenBelowParentItems groups keys root_pre upper_pre root_pre )
.

Definition sift_items_entail_wit_1_split_goal_2 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = n)) (PreH6 : ((Zlength (keys)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= upper_pre)) (PreH9 : (HeapOrderedExceptAtFromItems groups keys root_pre upper_pre root_pre )) (PreH10 : (ExtractionFrameItems groups keys (upper_pre + 1 ) )) ,
  (ParallelPermutation groups keys groups keys )
.

Definition sift_items_entail_wit_2_1 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) > upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) > upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_entail_wit_2_2 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) keys_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  (“ ((((2 * root ) + 1 ) + 1 ) > upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now ))
  ||
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) ) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
.

Definition sift_items_entail_wit_2_3 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) groups_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  (“ ((((2 * root ) + 1 ) + 1 ) > upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now ))
  ||
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) ) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
.

Definition sift_items_entail_wit_2_4 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) )) (PreH4 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH5 : (((2 * root ) + 1 ) <= upper_pre)) (PreH6 : (0 <= upper_pre)) (PreH7 : (upper_pre < n)) (PreH8 : (n <= cap)) (PreH9 : (cap <= 300000)) (PreH10 : ((Zlength (groups_now)) = n)) (PreH11 : ((Zlength (keys_now)) = n)) (PreH12 : (0 <= root_pre)) (PreH13 : (root_pre <= root)) (PreH14 : (root <= upper_pre)) (PreH15 : (0 <= ((2 * root ) + 1 ))) (PreH16 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) ) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
.

Definition sift_items_entail_wit_3_1 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) keys_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  (“ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) keys_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0)) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) groups_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0)) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
.

Definition sift_items_entail_wit_3_2 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) groups_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now)) = n)) (PreH12 : ((Zlength (keys_now)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  (EX (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) keys_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0)) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
  ||
  (“ (retval_2 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) groups_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0)) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
.

Definition sift_items_entail_wit_3_3 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = 0)) (PreH3 : (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) )) (PreH4 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH5 : (((2 * root ) + 1 ) <= upper_pre)) (PreH6 : (0 <= upper_pre)) (PreH7 : (upper_pre < n)) (PreH8 : (n <= cap)) (PreH9 : (cap <= 300000)) (PreH10 : ((Zlength (groups_now)) = n)) (PreH11 : ((Zlength (keys_now)) = n)) (PreH12 : (0 <= root_pre)) (PreH13 : (root_pre <= root)) (PreH14 : (root <= upper_pre)) (PreH15 : (0 <= ((2 * root ) + 1 ))) (PreH16 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  (EX (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) keys_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0)) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now 0) (Znth ((2 * root ) + 1 ) keys_now 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0) ) ” 
  &&  “ ((Znth ((2 * root ) + 1 ) groups_now 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0)) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now ))
.

Definition sift_items_entail_wit_4_1 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) keys_now_2 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now_2)) = n)) (PreH12 : ((Zlength (keys_now_2)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now_2 )
  **  (IntArray.full grp_pre n groups_now_2 )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= (((2 * root ) + 1 ) + 1 )) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre (((2 * root ) + 1 ) + 1 ) ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) keys_now_2 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now_2)) = n)) (PreH12 : ((Zlength (keys_now_2)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre (((2 * root ) + 1 ) + 1 ) ) ”
  &&  emp
).

Definition sift_items_entail_wit_4_1_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) keys_now_2 0) <> (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now_2)) = n)) (PreH12 : ((Zlength (keys_now_2)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre (((2 * root ) + 1 ) + 1 ) )
.

Definition sift_items_entail_wit_4_2 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) groups_now_2 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now_2)) = n)) (PreH12 : ((Zlength (keys_now_2)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now_2 )
  **  (IntArray.full grp_pre n groups_now_2 )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= (((2 * root ) + 1 ) + 1 )) ” 
  &&  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre (((2 * root ) + 1 ) + 1 ) ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) groups_now_2 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now_2)) = n)) (PreH12 : ((Zlength (keys_now_2)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre (((2 * root ) + 1 ) + 1 ) ) ”
  &&  emp
).

Definition sift_items_entail_wit_4_2_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) )) (PreH4 : ((Znth ((2 * root ) + 1 ) groups_now_2 0) <> (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0))) (PreH5 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH6 : (((2 * root ) + 1 ) <= upper_pre)) (PreH7 : (0 <= upper_pre)) (PreH8 : (upper_pre < n)) (PreH9 : (n <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups_now_2)) = n)) (PreH12 : ((Zlength (keys_now_2)) = n)) (PreH13 : (0 <= root_pre)) (PreH14 : (root_pre <= root)) (PreH15 : (root <= upper_pre)) (PreH16 : (0 <= ((2 * root ) + 1 ))) (PreH17 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH21 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH23 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre (((2 * root ) + 1 ) + 1 ) )
.

Definition sift_items_entail_wit_4_3 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) > upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now_2)) = n)) (PreH8 : ((Zlength (keys_now_2)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now_2 )
  **  (IntArray.full key_pre n keys_now_2 )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre ((2 * root ) + 1 ) ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) > upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now_2)) = n)) (PreH8 : ((Zlength (keys_now_2)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre ((2 * root ) + 1 ) ) ”
  &&  emp
).

Definition sift_items_entail_wit_4_3_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) > upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now_2)) = n)) (PreH8 : ((Zlength (keys_now_2)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre ((2 * root ) + 1 ) )
.

Definition sift_items_entail_wit_4_4 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) )) (PreH4 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH5 : (((2 * root ) + 1 ) <= upper_pre)) (PreH6 : (0 <= upper_pre)) (PreH7 : (upper_pre < n)) (PreH8 : (n <= cap)) (PreH9 : (cap <= 300000)) (PreH10 : ((Zlength (groups_now_2)) = n)) (PreH11 : ((Zlength (keys_now_2)) = n)) (PreH12 : (0 <= root_pre)) (PreH13 : (root_pre <= root)) (PreH14 : (root <= upper_pre)) (PreH15 : (0 <= ((2 * root ) + 1 ))) (PreH16 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now_2 )
  **  (IntArray.full grp_pre n groups_now_2 )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre ((2 * root ) + 1 ) ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) )) (PreH4 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH5 : (((2 * root ) + 1 ) <= upper_pre)) (PreH6 : (0 <= upper_pre)) (PreH7 : (upper_pre < n)) (PreH8 : (n <= cap)) (PreH9 : (cap <= 300000)) (PreH10 : ((Zlength (groups_now_2)) = n)) (PreH11 : ((Zlength (keys_now_2)) = n)) (PreH12 : (0 <= root_pre)) (PreH13 : (root_pre <= root)) (PreH14 : (root <= upper_pre)) (PreH15 : (0 <= ((2 * root ) + 1 ))) (PreH16 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre ((2 * root ) + 1 ) ) ”
  &&  emp
).

Definition sift_items_entail_wit_4_4_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth (((2 * root ) + 1 ) + 1 ) groups_now_2 0) (Znth (((2 * root ) + 1 ) + 1 ) keys_now_2 0) (Znth ((2 * root ) + 1 ) groups_now_2 0) (Znth ((2 * root ) + 1 ) keys_now_2 0) )) (PreH4 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH5 : (((2 * root ) + 1 ) <= upper_pre)) (PreH6 : (0 <= upper_pre)) (PreH7 : (upper_pre < n)) (PreH8 : (n <= cap)) (PreH9 : (cap <= 300000)) (PreH10 : ((Zlength (groups_now_2)) = n)) (PreH11 : ((Zlength (keys_now_2)) = n)) (PreH12 : (0 <= root_pre)) (PreH13 : (root_pre <= root)) (PreH14 : (root <= upper_pre)) (PreH15 : (0 <= ((2 * root ) + 1 ))) (PreH16 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre ((2 * root ) + 1 ) )
.

Definition sift_items_entail_wit_5_1 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) )
  **  ((( &( "t" ) )) # Int  |-> (Znth root keys_now_2 0))
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root < child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre child ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre child ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (keys))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ (ExtractionFrameItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) (upper_pre + 1 ) ) ” 
  &&  “ (SiftChildrenBelowParentItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child ) ” 
  &&  “ (HeapOrderedExceptAtFromItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) ) ” 
  &&  “ (root < child) ” 
  &&  “ ((Zlength ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = n) ” 
  &&  “ ((Zlength ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = n) ”
  &&  emp
).

Definition sift_items_entail_wit_5_1_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (keys)))
.

Definition sift_items_entail_wit_5_1_split_goal_2 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (groups)))
.

Definition sift_items_entail_wit_5_1_split_goal_3 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (ExtractionFrameItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) (upper_pre + 1 ) )
.

Definition sift_items_entail_wit_5_1_split_goal_4 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (SiftChildrenBelowParentItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child )
.

Definition sift_items_entail_wit_5_1_split_goal_5 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (HeapOrderedExceptAtFromItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child )
.

Definition sift_items_entail_wit_5_1_split_goal_6 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (ParallelPermutation groups keys (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) )
.

Definition sift_items_entail_wit_5_1_split_goal_7 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (root < child)
.

Definition sift_items_entail_wit_5_1_split_goal_8 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((Zlength ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = n)
.

Definition sift_items_entail_wit_5_1_split_goal_9 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root groups_now_2 0) <> (Znth child groups_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((Zlength ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = n)
.

Definition sift_items_entail_wit_5_2 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) )
  **  ((( &( "t" ) )) # Int  |-> (Znth root keys_now_2 0))
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root < child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre child ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre child ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (keys))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ (ExtractionFrameItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) (upper_pre + 1 ) ) ” 
  &&  “ (SiftChildrenBelowParentItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child ) ” 
  &&  “ (HeapOrderedExceptAtFromItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) ) ” 
  &&  “ (root < child) ” 
  &&  “ ((Zlength ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = n) ” 
  &&  “ ((Zlength ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = n) ”
  &&  emp
).

Definition sift_items_entail_wit_5_2_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (keys)))
.

Definition sift_items_entail_wit_5_2_split_goal_2 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((sublist ((upper_pre + 1 )) (n) ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = (sublist ((upper_pre + 1 )) (n) (groups)))
.

Definition sift_items_entail_wit_5_2_split_goal_3 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (ExtractionFrameItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) (upper_pre + 1 ) )
.

Definition sift_items_entail_wit_5_2_split_goal_4 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (SiftChildrenBelowParentItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child )
.

Definition sift_items_entail_wit_5_2_split_goal_5 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (HeapOrderedExceptAtFromItems (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) root_pre upper_pre child )
.

Definition sift_items_entail_wit_5_2_split_goal_6 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (ParallelPermutation groups keys (replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))) (replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))) )
.

Definition sift_items_entail_wit_5_2_split_goal_7 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (root < child)
.

Definition sift_items_entail_wit_5_2_split_goal_8 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((Zlength ((replace_Znth (child) ((Znth root keys_now_2 0)) ((replace_Znth (root) ((Znth child keys_now_2 0)) (keys_now_2)))))) = n)
.

Definition sift_items_entail_wit_5_2_split_goal_9 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now_2 0) (Znth root keys_now_2 0) (Znth child groups_now_2 0) (Znth child keys_now_2 0) )) (PreH4 : ((Znth root keys_now_2 0) <> (Znth child keys_now_2 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now_2)) = n)) (PreH10 : ((Zlength (keys_now_2)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now_2 keys_now_2 root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  ((Zlength ((replace_Znth (child) ((Znth root groups_now_2 0)) ((replace_Znth (root) ((Znth child groups_now_2 0)) (groups_now_2)))))) = n)
.

Definition sift_items_entail_wit_6 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (root: Z) (child: Z) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now_2)) = n)) (PreH6 : ((Zlength (keys_now_2)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root < child)) (PreH10 : (child <= upper_pre)) (PreH11 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH12 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 root_pre upper_pre child )) (PreH13 : (SiftChildrenBelowParentItems groups_now_2 keys_now_2 root_pre upper_pre child )) (PreH14 : (ExtractionFrameItems groups_now_2 keys_now_2 (upper_pre + 1 ) )) (PreH15 : ((sublist ((upper_pre + 1 )) (n) (groups_now_2)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH16 : ((sublist ((upper_pre + 1 )) (n) (keys_now_2)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now_2 )
  **  (IntArray.full key_pre n keys_now_2 )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (0 <= ((2 * child ) + 1 )) ” 
  &&  “ (((2 * child ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre child ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre child ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_return_wit_1 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth child groups_now 0) (Znth child keys_now 0) (Znth root groups_now 0) (Znth root keys_now 0) )) (PreH4 : (0 <= upper_pre)) (PreH5 : (upper_pre < n)) (PreH6 : (n <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups_now)) = n)) (PreH9 : ((Zlength (keys_now)) = n)) (PreH10 : (0 <= root_pre)) (PreH11 : (root_pre <= root)) (PreH12 : (root <= upper_pre)) (PreH13 : (0 <= child)) (PreH14 : (child <= upper_pre)) (PreH15 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH16 : (ParallelPermutation groups keys groups_now keys_now )) (PreH17 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH18 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH20 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  EX (keys_after: (@list Z))  (groups_after: (@list Z)) ,
  “ ((Zlength (groups_after)) = n) ” 
  &&  “ ((Zlength (keys_after)) = n) ” 
  &&  “ (ParallelPermutation groups keys groups_after keys_after ) ” 
  &&  “ (HeapParentsFromItems groups_after keys_after root_pre upper_pre ) ” 
  &&  “ (ExtractionFrameItems groups_after keys_after (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_after)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_after)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_after )
  **  (IntArray.full key_pre n keys_after )
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth child groups_now 0) (Znth child keys_now 0) (Znth root groups_now 0) (Znth root keys_now 0) )) (PreH4 : (0 <= upper_pre)) (PreH5 : (upper_pre < n)) (PreH6 : (n <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups_now)) = n)) (PreH9 : ((Zlength (keys_now)) = n)) (PreH10 : (0 <= root_pre)) (PreH11 : (root_pre <= root)) (PreH12 : (root <= upper_pre)) (PreH13 : (0 <= child)) (PreH14 : (child <= upper_pre)) (PreH15 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH16 : (ParallelPermutation groups keys groups_now keys_now )) (PreH17 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH18 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH20 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ (HeapParentsFromItems groups_now keys_now root_pre upper_pre ) ”
  &&  emp
).

Definition sift_items_return_wit_1_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (ItemLe4 (Znth child groups_now 0) (Znth child keys_now 0) (Znth root groups_now 0) (Znth root keys_now 0) )) (PreH4 : (0 <= upper_pre)) (PreH5 : (upper_pre < n)) (PreH6 : (n <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups_now)) = n)) (PreH9 : ((Zlength (keys_now)) = n)) (PreH10 : (0 <= root_pre)) (PreH11 : (root_pre <= root)) (PreH12 : (root <= upper_pre)) (PreH13 : (0 <= child)) (PreH14 : (child <= upper_pre)) (PreH15 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH16 : (ParallelPermutation groups keys groups_now keys_now )) (PreH17 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH18 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH20 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (HeapParentsFromItems groups_now keys_now root_pre upper_pre )
.

Definition sift_items_return_wit_2 := 
(
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) > upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  EX (keys_after: (@list Z))  (groups_after: (@list Z)) ,
  “ ((Zlength (groups_after)) = n) ” 
  &&  “ ((Zlength (keys_after)) = n) ” 
  &&  “ (ParallelPermutation groups keys groups_after keys_after ) ” 
  &&  “ (HeapParentsFromItems groups_after keys_after root_pre upper_pre ) ” 
  &&  “ (ExtractionFrameItems groups_after keys_after (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_after)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_after)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full grp_pre n groups_after )
  **  (IntArray.full key_pre n keys_after )
) \/
(
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) > upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  TT && emp 
|--
  “ (HeapParentsFromItems groups_now keys_now root_pre upper_pre ) ”
  &&  emp
).

Definition sift_items_return_wit_2_split_goal_1 := 
forall (upper_pre: Z) (root_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (((2 * root ) + 1 ) > upper_pre)) (PreH2 : (0 <= upper_pre)) (PreH3 : (upper_pre < n)) (PreH4 : (n <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_now)) = n)) (PreH7 : ((Zlength (keys_now)) = n)) (PreH8 : (0 <= root_pre)) (PreH9 : (root_pre <= root)) (PreH10 : (root <= upper_pre)) (PreH11 : (0 <= ((2 * root ) + 1 ))) (PreH12 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (HeapParentsFromItems groups_now keys_now root_pre upper_pre )
.

Definition sift_items_partial_solve_wit_1 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (((2 * root ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((2 * root ) + 1 ) groups_now 0))
  **  (IntArray.missing_i grp_pre ((2 * root ) + 1 ) 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_2 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (((2 * root ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((2 * root ) + 1 ) keys_now 0))
  **  (IntArray.missing_i key_pre ((2 * root ) + 1 ) 0 n keys_now )
  **  (IntArray.full grp_pre n groups_now )
.

Definition sift_items_partial_solve_wit_3 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + ((((2 * root ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth (((2 * root ) + 1 ) + 1 ) groups_now 0))
  **  (IntArray.missing_i grp_pre (((2 * root ) + 1 ) + 1 ) 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_4 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + ((((2 * root ) + 1 ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth (((2 * root ) + 1 ) + 1 ) keys_now 0))
  **  (IntArray.missing_i key_pre (((2 * root ) + 1 ) + 1 ) 0 n keys_now )
  **  (IntArray.full grp_pre n groups_now )
.

Definition sift_items_partial_solve_wit_5 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : ((((2 * root ) + 1 ) + 1 ) <= upper_pre)) (PreH2 : (((2 * root ) + 1 ) <= upper_pre)) (PreH3 : (0 <= upper_pre)) (PreH4 : (upper_pre < n)) (PreH5 : (n <= cap)) (PreH6 : (cap <= 300000)) (PreH7 : ((Zlength (groups_now)) = n)) (PreH8 : ((Zlength (keys_now)) = n)) (PreH9 : (0 <= root_pre)) (PreH10 : (root_pre <= root)) (PreH11 : (root <= upper_pre)) (PreH12 : (0 <= ((2 * root ) + 1 ))) (PreH13 : (((2 * root ) + 1 ) <= INT_MAX)) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH17 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH19 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  “ ((((2 * root ) + 1 ) + 1 ) <= upper_pre) ” 
  &&  “ (((2 * root ) + 1 ) <= upper_pre) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= ((2 * root ) + 1 )) ” 
  &&  “ (((2 * root ) + 1 ) <= INT_MAX) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
.

Definition sift_items_partial_solve_wit_6 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= child)) (PreH11 : (child <= upper_pre)) (PreH12 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (root * sizeof(INT)))) # Int  |-> (Znth root groups_now 0))
  **  (IntArray.missing_i grp_pre root 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_7 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= child)) (PreH11 : (child <= upper_pre)) (PreH12 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (root * sizeof(INT)))) # Int  |-> (Znth root keys_now 0))
  **  (IntArray.missing_i key_pre root 0 n keys_now )
  **  (IntArray.full grp_pre n groups_now )
.

Definition sift_items_partial_solve_wit_8 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= child)) (PreH11 : (child <= upper_pre)) (PreH12 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (child * sizeof(INT)))) # Int  |-> (Znth child groups_now 0))
  **  (IntArray.missing_i grp_pre child 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_9 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= child)) (PreH11 : (child <= upper_pre)) (PreH12 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child keys_now 0))
  **  (IntArray.missing_i key_pre child 0 n keys_now )
  **  (IntArray.full grp_pre n groups_now )
.

Definition sift_items_partial_solve_wit_10 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (PreH1 : (0 <= upper_pre)) (PreH2 : (upper_pre < n)) (PreH3 : (n <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_now)) = n)) (PreH6 : ((Zlength (keys_now)) = n)) (PreH7 : (0 <= root_pre)) (PreH8 : (root_pre <= root)) (PreH9 : (root <= upper_pre)) (PreH10 : (0 <= child)) (PreH11 : (child <= upper_pre)) (PreH12 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH13 : (ParallelPermutation groups keys groups_now keys_now )) (PreH14 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH15 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH16 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH17 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH18 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
.

Definition sift_items_partial_solve_wit_11 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (root * sizeof(INT)))) # Int  |-> (Znth root groups_now 0))
  **  (IntArray.missing_i grp_pre root 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_12 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n groups_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (root * sizeof(INT)))) # Int  |-> (Znth root groups_now 0))
  **  (IntArray.missing_i grp_pre root 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_13 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (child * sizeof(INT)))) # Int  |-> (Znth child groups_now 0))
  **  (IntArray.missing_i grp_pre child 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_14 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (root * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i grp_pre root 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_15 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (child * sizeof(INT)))) # Int  |-> (Znth child groups_now 0))
  **  (IntArray.missing_i grp_pre child 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_16 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n groups_now )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (root * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i grp_pre root 0 n groups_now )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_17 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n (replace_Znth (root) ((Znth child groups_now 0)) (groups_now)) )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i grp_pre child 0 n (replace_Znth (root) ((Znth child groups_now 0)) (groups_now)) )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_18 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n (replace_Znth (root) ((Znth child groups_now 0)) (groups_now)) )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((grp_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i grp_pre child 0 n (replace_Znth (root) ((Znth child groups_now 0)) (groups_now)) )
  **  (IntArray.full key_pre n keys_now )
.

Definition sift_items_partial_solve_wit_19 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (root * sizeof(INT)))) # Int  |-> (Znth root keys_now 0))
  **  (IntArray.missing_i key_pre root 0 n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

Definition sift_items_partial_solve_wit_20 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
  **  (IntArray.full key_pre n keys_now )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (root * sizeof(INT)))) # Int  |-> (Znth root keys_now 0))
  **  (IntArray.missing_i key_pre root 0 n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

Definition sift_items_partial_solve_wit_21 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child keys_now 0))
  **  (IntArray.missing_i key_pre child 0 n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

Definition sift_items_partial_solve_wit_22 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (root * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre root 0 n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

Definition sift_items_partial_solve_wit_23 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |-> (Znth child keys_now 0))
  **  (IntArray.missing_i key_pre child 0 n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

Definition sift_items_partial_solve_wit_24 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (root * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre root 0 n keys_now )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

Definition sift_items_partial_solve_wit_25 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root groups_now 0) <> (Znth child groups_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n (replace_Znth (root) ((Znth child keys_now 0)) (keys_now)) )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root groups_now 0) <> (Znth child groups_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre child 0 n (replace_Znth (root) ((Znth child keys_now 0)) (keys_now)) )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

Definition sift_items_partial_solve_wit_26 := 
forall (upper_pre: Z) (root_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (n: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (root: Z) (child: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) )) (PreH4 : ((Znth root keys_now 0) <> (Znth child keys_now 0))) (PreH5 : (0 <= upper_pre)) (PreH6 : (upper_pre < n)) (PreH7 : (n <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups_now)) = n)) (PreH10 : ((Zlength (keys_now)) = n)) (PreH11 : (0 <= root_pre)) (PreH12 : (root_pre <= root)) (PreH13 : (root <= upper_pre)) (PreH14 : (0 <= child)) (PreH15 : (child <= upper_pre)) (PreH16 : (SelectedLargerChildItems groups_now keys_now root upper_pre child )) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root )) (PreH19 : (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root )) (PreH20 : (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) )) (PreH21 : ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups)))) (PreH22 : ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys)))) ,
  (IntArray.full key_pre n (replace_Znth (root) ((Znth child keys_now 0)) (keys_now)) )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (ItemLe4 (Znth root groups_now 0) (Znth root keys_now 0) (Znth child groups_now 0) (Znth child keys_now 0) ) ” 
  &&  “ ((Znth root keys_now 0) <> (Znth child keys_now 0)) ” 
  &&  “ (0 <= upper_pre) ” 
  &&  “ (upper_pre < n) ” 
  &&  “ (n <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = n) ” 
  &&  “ ((Zlength (keys_now)) = n) ” 
  &&  “ (0 <= root_pre) ” 
  &&  “ (root_pre <= root) ” 
  &&  “ (root <= upper_pre) ” 
  &&  “ (0 <= child) ” 
  &&  “ (child <= upper_pre) ” 
  &&  “ (SelectedLargerChildItems groups_now keys_now root upper_pre child ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (SiftChildrenBelowParentItems groups_now keys_now root_pre upper_pre root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now (upper_pre + 1 ) ) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (groups_now)) = (sublist ((upper_pre + 1 )) (n) (groups))) ” 
  &&  “ ((sublist ((upper_pre + 1 )) (n) (keys_now)) = (sublist ((upper_pre + 1 )) (n) (keys))) ”
  &&  (((key_pre + (child * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre child 0 n (replace_Znth (root) ((Znth child keys_now 0)) (keys_now)) )
  **  (IntArray.full grp_pre n (replace_Znth (child) ((Znth root groups_now 0)) ((replace_Znth (root) ((Znth child groups_now 0)) (groups_now)))) )
.

(*----- Function sort_items -----*)

Definition sort_items_safety_wit_1 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ (((cnt_pre ÷ 2 ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cnt_pre ÷ 2 ) - 1 )) ”
) \/
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ (((cnt_pre ÷ 2 ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cnt_pre ÷ 2 ) - 1 )) ”
).

Definition sort_items_safety_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ (((cnt_pre ÷ 2 ) - 1 ) <= INT_MAX) ”
.

Definition sort_items_safety_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ ((INT_MIN) <= ((cnt_pre ÷ 2 ) - 1 )) ”
.

Definition sort_items_safety_wit_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ ((cnt_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition sort_items_safety_wit_3 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sort_items_safety_wit_4 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "root" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_items_safety_wit_5 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) (PreH6 : ((Zlength (groups_now)) = cnt_pre)) (PreH7 : ((Zlength (keys_now)) = cnt_pre)) (PreH8 : ((-1) <= root)) (PreH9 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH10 : (ParallelPermutation groups keys groups_now keys_now )) (PreH11 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_items_safety_wit_6 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now keys_now groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after root (cnt_pre - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((cnt_pre - 1 ) + 1 ) )) (PreH6 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_now)))) (PreH7 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_now)))) (PreH8 : (root >= 0)) (PreH9 : (0 <= cnt_pre)) (PreH10 : (cnt_pre <= cap)) (PreH11 : (cap <= 300000)) (PreH12 : ((Zlength (groups)) = cnt_pre)) (PreH13 : ((Zlength (keys)) = cnt_pre)) (PreH14 : ((Zlength (groups_now)) = cnt_pre)) (PreH15 : ((Zlength (keys_now)) = cnt_pre)) (PreH16 : ((-1) <= root)) (PreH17 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH18 : (ParallelPermutation groups keys groups_now keys_now )) (PreH19 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
|--
  “ ((root - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (root - 1 )) ”
.

Definition sort_items_safety_wit_7 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root >= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now keys_now )) (PreH12 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ ((cnt_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt_pre - 1 )) ”
.

Definition sort_items_safety_wit_8 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root >= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now keys_now )) (PreH12 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_items_safety_wit_9 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now keys_now )) (PreH12 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "upper" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ ((cnt_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt_pre - 1 )) ”
.

Definition sort_items_safety_wit_10 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now keys_now )) (PreH12 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "upper" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_items_safety_wit_11 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) (PreH6 : ((Zlength (groups_now)) = cnt_pre)) (PreH7 : ((Zlength (keys_now)) = cnt_pre)) (PreH8 : ((-1) <= upper)) (PreH9 : (upper < cnt_pre)) (PreH10 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_items_safety_wit_12 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_items_safety_wit_13 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre groups_now )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 groups_now 0))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_items_safety_wit_14 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 groups_now 0))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_items_safety_wit_15 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full key_pre cnt_pre keys_now )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 keys_now 0))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_items_safety_wit_16 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) (PreH6 : ((Zlength (groups_now)) = cnt_pre)) (PreH7 : ((Zlength (keys_now)) = cnt_pre)) (PreH8 : (1 <= upper)) (PreH9 : (upper <= (cnt_pre - 1 ))) (PreH10 : (ParallelPermutation groups keys groups_now keys_now )) (PreH11 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH12 : (ExtractionFrameItems groups_now keys_now upper )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
|--
  “ ((upper - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper - 1 )) ”
.

Definition sort_items_safety_wit_17 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) (PreH6 : ((Zlength (groups_now)) = cnt_pre)) (PreH7 : ((Zlength (keys_now)) = cnt_pre)) (PreH8 : (1 <= upper)) (PreH9 : (upper <= (cnt_pre - 1 ))) (PreH10 : (ParallelPermutation groups keys groups_now keys_now )) (PreH11 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH12 : (ExtractionFrameItems groups_now keys_now upper )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sort_items_safety_wit_18 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) (PreH6 : ((Zlength (groups_now)) = cnt_pre)) (PreH7 : ((Zlength (keys_now)) = cnt_pre)) (PreH8 : (1 <= upper)) (PreH9 : (upper <= (cnt_pre - 1 ))) (PreH10 : (ParallelPermutation groups keys groups_now keys_now )) (PreH11 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH12 : (ExtractionFrameItems groups_now keys_now upper )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sort_items_safety_wit_19 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now keys_now groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after 0 (upper - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((upper - 1 ) + 1 ) )) (PreH6 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_now)))) (PreH7 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_now)))) (PreH8 : (0 <= cnt_pre)) (PreH9 : (cnt_pre <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups)) = cnt_pre)) (PreH12 : ((Zlength (keys)) = cnt_pre)) (PreH13 : ((Zlength (groups_now)) = cnt_pre)) (PreH14 : ((Zlength (keys_now)) = cnt_pre)) (PreH15 : (1 <= upper)) (PreH16 : (upper <= (cnt_pre - 1 ))) (PreH17 : (ParallelPermutation groups keys groups_now keys_now )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH19 : (ExtractionFrameItems groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
|--
  “ ((upper - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper - 1 )) ”
.

Definition sort_items_entail_wit_1 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= ((cnt_pre ÷ 2 ) - 1 )) ” 
  &&  “ (((cnt_pre ÷ 2 ) - 1 ) <= ((cnt_pre ÷ 2 ) - 1 )) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapParentsFromItems groups_now keys_now (((cnt_pre ÷ 2 ) - 1 ) + 1 ) (cnt_pre - 1 ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  TT && emp 
|--
  “ (HeapParentsFromItems groups keys (((cnt_pre ÷ 2 ) - 1 ) + 1 ) (cnt_pre - 1 ) ) ” 
  &&  “ (ParallelPermutation groups keys groups keys ) ” 
  &&  “ ((-1) <= ((cnt_pre ÷ 2 ) - 1 )) ”
  &&  emp
).

Definition sort_items_entail_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  (HeapParentsFromItems groups keys (((cnt_pre ÷ 2 ) - 1 ) + 1 ) (cnt_pre - 1 ) )
.

Definition sort_items_entail_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  (ParallelPermutation groups keys groups keys )
.

Definition sort_items_entail_wit_1_split_goal_3 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((-1) <= ((cnt_pre ÷ 2 ) - 1 ))
.

Definition sort_items_entail_wit_2 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now_2 keys_now_2 groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after root (cnt_pre - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((cnt_pre - 1 ) + 1 ) )) (PreH6 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_now_2)))) (PreH7 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_now_2)))) (PreH8 : (root >= 0)) (PreH9 : (0 <= cnt_pre)) (PreH10 : (cnt_pre <= cap)) (PreH11 : (cap <= 300000)) (PreH12 : ((Zlength (groups)) = cnt_pre)) (PreH13 : ((Zlength (keys)) = cnt_pre)) (PreH14 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH15 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH16 : ((-1) <= root)) (PreH17 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapParentsFromItems groups_now_2 keys_now_2 (root + 1 ) (cnt_pre - 1 ) )) ,
  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= (root - 1 )) ” 
  &&  “ ((root - 1 ) <= ((cnt_pre ÷ 2 ) - 1 )) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapParentsFromItems groups_now keys_now ((root - 1 ) + 1 ) (cnt_pre - 1 ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now_2 keys_now_2 groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after root (cnt_pre - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((cnt_pre - 1 ) + 1 ) )) (PreH6 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_now_2)))) (PreH7 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_now_2)))) (PreH8 : (root >= 0)) (PreH9 : (0 <= cnt_pre)) (PreH10 : (cnt_pre <= cap)) (PreH11 : (cap <= 300000)) (PreH12 : ((Zlength (groups)) = cnt_pre)) (PreH13 : ((Zlength (keys)) = cnt_pre)) (PreH14 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH15 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH16 : ((-1) <= root)) (PreH17 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapParentsFromItems groups_now_2 keys_now_2 (root + 1 ) (cnt_pre - 1 ) )) ,
  TT && emp 
|--
  “ (HeapParentsFromItems groups_after keys_after ((root - 1 ) + 1 ) (cnt_pre - 1 ) ) ” 
  &&  “ (ParallelPermutation groups keys groups_after keys_after ) ”
  &&  emp
).

Definition sort_items_entail_wit_2_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now_2 keys_now_2 groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after root (cnt_pre - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((cnt_pre - 1 ) + 1 ) )) (PreH6 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_now_2)))) (PreH7 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_now_2)))) (PreH8 : (root >= 0)) (PreH9 : (0 <= cnt_pre)) (PreH10 : (cnt_pre <= cap)) (PreH11 : (cap <= 300000)) (PreH12 : ((Zlength (groups)) = cnt_pre)) (PreH13 : ((Zlength (keys)) = cnt_pre)) (PreH14 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH15 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH16 : ((-1) <= root)) (PreH17 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapParentsFromItems groups_now_2 keys_now_2 (root + 1 ) (cnt_pre - 1 ) )) ,
  (HeapParentsFromItems groups_after keys_after ((root - 1 ) + 1 ) (cnt_pre - 1 ) )
.

Definition sort_items_entail_wit_2_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now_2 keys_now_2 groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after root (cnt_pre - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((cnt_pre - 1 ) + 1 ) )) (PreH6 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (groups_now_2)))) (PreH7 : ((sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((cnt_pre - 1 ) + 1 )) (cnt_pre) (keys_now_2)))) (PreH8 : (root >= 0)) (PreH9 : (0 <= cnt_pre)) (PreH10 : (cnt_pre <= cap)) (PreH11 : (cap <= 300000)) (PreH12 : ((Zlength (groups)) = cnt_pre)) (PreH13 : ((Zlength (keys)) = cnt_pre)) (PreH14 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH15 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH16 : ((-1) <= root)) (PreH17 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH18 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH19 : (HeapParentsFromItems groups_now_2 keys_now_2 (root + 1 ) (cnt_pre - 1 ) )) ,
  (ParallelPermutation groups keys groups_after keys_after )
.

Definition sort_items_entail_wit_3 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH12 : (HeapParentsFromItems groups_now_2 keys_now_2 (root + 1 ) (cnt_pre - 1 ) )) ,
  (IntArray.full grp_pre cnt_pre groups_now_2 )
  **  (IntArray.full key_pre cnt_pre keys_now_2 )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= (cnt_pre - 1 )) ” 
  &&  “ ((cnt_pre - 1 ) < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now (cnt_pre - 1 ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH12 : (HeapParentsFromItems groups_now_2 keys_now_2 (root + 1 ) (cnt_pre - 1 ) )) ,
  TT && emp 
|--
  “ (HeapSortItemsState groups keys groups_now_2 keys_now_2 (cnt_pre - 1 ) ) ”
  &&  emp
).

Definition sort_items_entail_wit_3_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (root < 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH12 : (HeapParentsFromItems groups_now_2 keys_now_2 (root + 1 ) (cnt_pre - 1 ) )) ,
  (HeapSortItemsState groups keys groups_now_2 keys_now_2 (cnt_pre - 1 ) )
.

Definition sort_items_entail_wit_4 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now_2 keys_now_2 upper )) ,
  (IntArray.full key_pre cnt_pre (replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))) )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))) )
  **  ((( &( "t" ) )) # Int  |-> (Znth 0 keys_now_2 0))
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ (1 <= upper) ” 
  &&  “ (upper <= (cnt_pre - 1 )) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now upper ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now_2 keys_now_2 upper )) ,
  TT && emp 
|--
  “ (ExtractionFrameItems (replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))) (replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))) upper ) ” 
  &&  “ (HeapOrderedExceptAtFromItems (replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))) (replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))) 0 (upper - 1 ) 0 ) ” 
  &&  “ (ParallelPermutation groups keys (replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))) (replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))) ) ” 
  &&  “ ((Zlength ((replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))))) = cnt_pre) ” 
  &&  “ ((Zlength ((replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))))) = cnt_pre) ”
  &&  emp
).

Definition sort_items_entail_wit_4_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now_2 keys_now_2 upper )) ,
  (ExtractionFrameItems (replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))) (replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))) upper )
.

Definition sort_items_entail_wit_4_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now_2 keys_now_2 upper )) ,
  (HeapOrderedExceptAtFromItems (replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))) (replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))) 0 (upper - 1 ) 0 )
.

Definition sort_items_entail_wit_4_split_goal_3 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now_2 keys_now_2 upper )) ,
  (ParallelPermutation groups keys (replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))) (replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))) )
.

Definition sort_items_entail_wit_4_split_goal_4 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now_2 keys_now_2 upper )) ,
  ((Zlength ((replace_Znth (upper) ((Znth 0 keys_now_2 0)) ((replace_Znth (0) ((Znth upper keys_now_2 0)) (keys_now_2)))))) = cnt_pre)
.

Definition sort_items_entail_wit_4_split_goal_5 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now_2: (@list Z)) (groups_now_2: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH8 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now_2 keys_now_2 upper )) ,
  ((Zlength ((replace_Znth (upper) ((Znth 0 groups_now_2 0)) ((replace_Znth (0) ((Znth upper groups_now_2 0)) (groups_now_2)))))) = cnt_pre)
.

Definition sort_items_entail_wit_5 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (upper: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now_2 keys_now_2 groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after 0 (upper - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((upper - 1 ) + 1 ) )) (PreH6 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_now_2)))) (PreH7 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_now_2)))) (PreH8 : (0 <= cnt_pre)) (PreH9 : (cnt_pre <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups)) = cnt_pre)) (PreH12 : ((Zlength (keys)) = cnt_pre)) (PreH13 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH14 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH15 : (1 <= upper)) (PreH16 : (upper <= (cnt_pre - 1 ))) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 0 (upper - 1 ) 0 )) (PreH19 : (ExtractionFrameItems groups_now_2 keys_now_2 upper )) ,
  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
|--
  EX (keys_now: (@list Z))  (groups_now: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= (upper - 1 )) ” 
  &&  “ ((upper - 1 ) < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now (upper - 1 ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (upper: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now_2 keys_now_2 groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after 0 (upper - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((upper - 1 ) + 1 ) )) (PreH6 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_now_2)))) (PreH7 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_now_2)))) (PreH8 : (0 <= cnt_pre)) (PreH9 : (cnt_pre <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups)) = cnt_pre)) (PreH12 : ((Zlength (keys)) = cnt_pre)) (PreH13 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH14 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH15 : (1 <= upper)) (PreH16 : (upper <= (cnt_pre - 1 ))) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 0 (upper - 1 ) 0 )) (PreH19 : (ExtractionFrameItems groups_now_2 keys_now_2 upper )) ,
  TT && emp 
|--
  “ (HeapSortItemsState groups keys groups_after keys_after (upper - 1 ) ) ”
  &&  emp
).

Definition sort_items_entail_wit_5_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now_2: (@list Z)) (keys_now_2: (@list Z)) (upper: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups_now_2 keys_now_2 groups_after keys_after )) (PreH4 : (HeapParentsFromItems groups_after keys_after 0 (upper - 1 ) )) (PreH5 : (ExtractionFrameItems groups_after keys_after ((upper - 1 ) + 1 ) )) (PreH6 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (groups_now_2)))) (PreH7 : ((sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_after)) = (sublist (((upper - 1 ) + 1 )) (cnt_pre) (keys_now_2)))) (PreH8 : (0 <= cnt_pre)) (PreH9 : (cnt_pre <= cap)) (PreH10 : (cap <= 300000)) (PreH11 : ((Zlength (groups)) = cnt_pre)) (PreH12 : ((Zlength (keys)) = cnt_pre)) (PreH13 : ((Zlength (groups_now_2)) = cnt_pre)) (PreH14 : ((Zlength (keys_now_2)) = cnt_pre)) (PreH15 : (1 <= upper)) (PreH16 : (upper <= (cnt_pre - 1 ))) (PreH17 : (ParallelPermutation groups keys groups_now_2 keys_now_2 )) (PreH18 : (HeapOrderedExceptAtFromItems groups_now_2 keys_now_2 0 (upper - 1 ) 0 )) (PreH19 : (ExtractionFrameItems groups_now_2 keys_now_2 upper )) ,
  (HeapSortItemsState groups keys groups_after keys_after (upper - 1 ) )
.

Definition sort_items_return_wit_1 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper <= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  EX (keys_after: (@list Z))  (groups_after: (@list Z)) ,
  “ ((Zlength (groups_after)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_after)) = cnt_pre) ” 
  &&  “ (ParallelPermutation groups keys groups_after keys_after ) ” 
  &&  “ (ItemsIncreasing groups_after keys_after ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper <= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  TT && emp 
|--
  “ (ItemsIncreasing groups_now keys_now ) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ”
  &&  emp
).

Definition sort_items_return_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper <= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (ItemsIncreasing groups_now keys_now )
.

Definition sort_items_return_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper <= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (ParallelPermutation groups keys groups_now keys_now )
.

Definition sort_items_partial_solve_wit_1_pure := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root >= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now keys_now )) (PreH12 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ ((cnt_pre - 1 ) < cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now ((cnt_pre - 1 ) + 1 ) ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root (cnt_pre - 1 ) root ) ” 
  &&  “ (root <= (cnt_pre - 1 )) ” 
  &&  “ (0 <= (cnt_pre - 1 )) ”
) \/
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root <= INT_MAX)) (PreH2 : (cnt_pre <= INT_MAX)) (PreH3 : (root >= INT_MIN)) (PreH4 : (cnt_pre >= INT_MIN)) (PreH5 : (root >= 0)) (PreH6 : (0 <= cnt_pre)) (PreH7 : (cnt_pre <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups)) = cnt_pre)) (PreH10 : ((Zlength (keys)) = cnt_pre)) (PreH11 : ((Zlength (groups_now)) = cnt_pre)) (PreH12 : ((Zlength (keys_now)) = cnt_pre)) (PreH13 : ((-1) <= root)) (PreH14 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation groups keys groups_now keys_now )) (PreH16 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= (cnt_pre - 1 )) ” 
  &&  “ (root <= (cnt_pre - 1 )) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root (cnt_pre - 1 ) root ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now ((cnt_pre - 1 ) + 1 ) ) ”
).

Definition sort_items_partial_solve_wit_1_pure_split_goal_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root <= INT_MAX)) (PreH2 : (cnt_pre <= INT_MAX)) (PreH3 : (root >= INT_MIN)) (PreH4 : (cnt_pre >= INT_MIN)) (PreH5 : (root >= 0)) (PreH6 : (0 <= cnt_pre)) (PreH7 : (cnt_pre <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups)) = cnt_pre)) (PreH10 : ((Zlength (keys)) = cnt_pre)) (PreH11 : ((Zlength (groups_now)) = cnt_pre)) (PreH12 : ((Zlength (keys_now)) = cnt_pre)) (PreH13 : ((-1) <= root)) (PreH14 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation groups keys groups_now keys_now )) (PreH16 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= (cnt_pre - 1 )) ”
.

Definition sort_items_partial_solve_wit_1_pure_split_goal_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root <= INT_MAX)) (PreH2 : (cnt_pre <= INT_MAX)) (PreH3 : (root >= INT_MIN)) (PreH4 : (cnt_pre >= INT_MIN)) (PreH5 : (root >= 0)) (PreH6 : (0 <= cnt_pre)) (PreH7 : (cnt_pre <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups)) = cnt_pre)) (PreH10 : ((Zlength (keys)) = cnt_pre)) (PreH11 : ((Zlength (groups_now)) = cnt_pre)) (PreH12 : ((Zlength (keys_now)) = cnt_pre)) (PreH13 : ((-1) <= root)) (PreH14 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation groups keys groups_now keys_now )) (PreH16 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (root <= (cnt_pre - 1 )) ”
.

Definition sort_items_partial_solve_wit_1_pure_split_goal_3 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root <= INT_MAX)) (PreH2 : (cnt_pre <= INT_MAX)) (PreH3 : (root >= INT_MIN)) (PreH4 : (cnt_pre >= INT_MIN)) (PreH5 : (root >= 0)) (PreH6 : (0 <= cnt_pre)) (PreH7 : (cnt_pre <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups)) = cnt_pre)) (PreH10 : ((Zlength (keys)) = cnt_pre)) (PreH11 : ((Zlength (groups_now)) = cnt_pre)) (PreH12 : ((Zlength (keys_now)) = cnt_pre)) (PreH13 : ((-1) <= root)) (PreH14 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation groups keys groups_now keys_now )) (PreH16 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (HeapOrderedExceptAtFromItems groups_now keys_now root (cnt_pre - 1 ) root ) ”
.

Definition sort_items_partial_solve_wit_1_pure_split_goal_4 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root <= INT_MAX)) (PreH2 : (cnt_pre <= INT_MAX)) (PreH3 : (root >= INT_MIN)) (PreH4 : (cnt_pre >= INT_MIN)) (PreH5 : (root >= 0)) (PreH6 : (0 <= cnt_pre)) (PreH7 : (cnt_pre <= cap)) (PreH8 : (cap <= 300000)) (PreH9 : ((Zlength (groups)) = cnt_pre)) (PreH10 : ((Zlength (keys)) = cnt_pre)) (PreH11 : ((Zlength (groups_now)) = cnt_pre)) (PreH12 : ((Zlength (keys_now)) = cnt_pre)) (PreH13 : ((-1) <= root)) (PreH14 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH15 : (ParallelPermutation groups keys groups_now keys_now )) (PreH16 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "root" ) )) # Int  |-> root)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (ExtractionFrameItems groups_now keys_now ((cnt_pre - 1 ) + 1 ) ) ”
.

Definition sort_items_partial_solve_wit_1_aux := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (root: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (root >= 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= root)) (PreH10 : (root <= ((cnt_pre ÷ 2 ) - 1 ))) (PreH11 : (ParallelPermutation groups keys groups_now keys_now )) (PreH12 : (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) )) ,
  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ ((cnt_pre - 1 ) < cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ (0 <= root) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now ((cnt_pre - 1 ) + 1 ) ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now root (cnt_pre - 1 ) root ) ” 
  &&  “ (root <= (cnt_pre - 1 )) ” 
  &&  “ (0 <= (cnt_pre - 1 )) ” 
  &&  “ (root >= 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= root) ” 
  &&  “ (root <= ((cnt_pre ÷ 2 ) - 1 )) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapParentsFromItems groups_now keys_now (root + 1 ) (cnt_pre - 1 ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
.

Definition sort_items_partial_solve_wit_1 := sort_items_partial_solve_wit_1_pure -> sort_items_partial_solve_wit_1_aux.

Definition sort_items_partial_solve_wit_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((grp_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 groups_now 0))
  **  (IntArray.missing_i grp_pre 0 0 cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
.

Definition sort_items_partial_solve_wit_3 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((grp_pre + (upper * sizeof(INT)))) # Int  |-> (Znth upper groups_now 0))
  **  (IntArray.missing_i grp_pre upper 0 cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
.

Definition sort_items_partial_solve_wit_4 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((grp_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i grp_pre 0 0 cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
.

Definition sort_items_partial_solve_wit_5 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre (replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)) )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((grp_pre + (upper * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i grp_pre upper 0 cnt_pre (replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)) )
  **  (IntArray.full key_pre cnt_pre keys_now )
.

Definition sort_items_partial_solve_wit_6 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((key_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 keys_now 0))
  **  (IntArray.missing_i key_pre 0 0 cnt_pre keys_now )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
.

Definition sort_items_partial_solve_wit_7 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full key_pre cnt_pre keys_now )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((key_pre + (upper * sizeof(INT)))) # Int  |-> (Znth upper keys_now 0))
  **  (IntArray.missing_i key_pre upper 0 cnt_pre keys_now )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
.

Definition sort_items_partial_solve_wit_8 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full key_pre cnt_pre keys_now )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((key_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre 0 0 cnt_pre keys_now )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
.

Definition sort_items_partial_solve_wit_9 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (upper: Z) (keys_now: (@list Z)) (groups_now: (@list Z)) (PreH1 : (upper > 0)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups)) = cnt_pre)) (PreH6 : ((Zlength (keys)) = cnt_pre)) (PreH7 : ((Zlength (groups_now)) = cnt_pre)) (PreH8 : ((Zlength (keys_now)) = cnt_pre)) (PreH9 : ((-1) <= upper)) (PreH10 : (upper < cnt_pre)) (PreH11 : (HeapSortItemsState groups keys groups_now keys_now upper )) ,
  (IntArray.full key_pre cnt_pre (replace_Znth (0) ((Znth upper keys_now 0)) (keys_now)) )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
|--
  “ (upper > 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ ((-1) <= upper) ” 
  &&  “ (upper < cnt_pre) ” 
  &&  “ (HeapSortItemsState groups keys groups_now keys_now upper ) ”
  &&  (((key_pre + (upper * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i key_pre upper 0 cnt_pre (replace_Znth (0) ((Znth upper keys_now 0)) (keys_now)) )
  **  (IntArray.full grp_pre cnt_pre (replace_Znth (upper) ((Znth 0 groups_now 0)) ((replace_Znth (0) ((Znth upper groups_now 0)) (groups_now)))) )
.

Definition sort_items_partial_solve_wit_10_pure := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) (PreH6 : ((Zlength (groups_now)) = cnt_pre)) (PreH7 : ((Zlength (keys_now)) = cnt_pre)) (PreH8 : (1 <= upper)) (PreH9 : (upper <= (cnt_pre - 1 ))) (PreH10 : (ParallelPermutation groups keys groups_now keys_now )) (PreH11 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH12 : (ExtractionFrameItems groups_now keys_now upper )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
|--
  “ (0 <= (upper - 1 )) ” 
  &&  “ ((upper - 1 ) < cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (upper - 1 )) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now ((upper - 1 ) + 1 ) ) ”
) \/
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (PreH1 : (upper <= INT_MAX)) (PreH2 : (cnt_pre <= INT_MAX)) (PreH3 : (upper >= INT_MIN)) (PreH4 : (cnt_pre >= INT_MIN)) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) (PreH10 : ((Zlength (groups_now)) = cnt_pre)) (PreH11 : ((Zlength (keys_now)) = cnt_pre)) (PreH12 : (1 <= upper)) (PreH13 : (upper <= (cnt_pre - 1 ))) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH16 : (ExtractionFrameItems groups_now keys_now upper )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
|--
  “ (ExtractionFrameItems groups_now keys_now ((upper - 1 ) + 1 ) ) ”
).

Definition sort_items_partial_solve_wit_10_pure_split_goal_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (PreH1 : (upper <= INT_MAX)) (PreH2 : (cnt_pre <= INT_MAX)) (PreH3 : (upper >= INT_MIN)) (PreH4 : (cnt_pre >= INT_MIN)) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) (PreH10 : ((Zlength (groups_now)) = cnt_pre)) (PreH11 : ((Zlength (keys_now)) = cnt_pre)) (PreH12 : (1 <= upper)) (PreH13 : (upper <= (cnt_pre - 1 ))) (PreH14 : (ParallelPermutation groups keys groups_now keys_now )) (PreH15 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH16 : (ExtractionFrameItems groups_now keys_now upper )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
  **  ((( &( "t" ) )) # Int  |->_)
|--
  “ (ExtractionFrameItems groups_now keys_now ((upper - 1 ) + 1 ) ) ”
.

Definition sort_items_partial_solve_wit_10_aux := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (groups_now: (@list Z)) (keys_now: (@list Z)) (upper: Z) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) (PreH6 : ((Zlength (groups_now)) = cnt_pre)) (PreH7 : ((Zlength (keys_now)) = cnt_pre)) (PreH8 : (1 <= upper)) (PreH9 : (upper <= (cnt_pre - 1 ))) (PreH10 : (ParallelPermutation groups keys groups_now keys_now )) (PreH11 : (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 )) (PreH12 : (ExtractionFrameItems groups_now keys_now upper )) ,
  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
|--
  “ (0 <= (upper - 1 )) ” 
  &&  “ ((upper - 1 ) < cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (upper - 1 )) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now ((upper - 1 ) + 1 ) ) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ ((Zlength (groups_now)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_now)) = cnt_pre) ” 
  &&  “ (1 <= upper) ” 
  &&  “ (upper <= (cnt_pre - 1 )) ” 
  &&  “ (ParallelPermutation groups keys groups_now keys_now ) ” 
  &&  “ (HeapOrderedExceptAtFromItems groups_now keys_now 0 (upper - 1 ) 0 ) ” 
  &&  “ (ExtractionFrameItems groups_now keys_now upper ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_now )
  **  (IntArray.full key_pre cnt_pre keys_now )
.

Definition sort_items_partial_solve_wit_10 := sort_items_partial_solve_wit_10_pure -> sort_items_partial_solve_wit_10_aux.

(*----- Function count_pairs -----*)

Definition count_pairs_safety_wit_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups keys groups_after keys_after )) (PreH4 : (ItemsIncreasing groups_after keys_after )) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_pairs_safety_wit_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups keys groups_after keys_after )) (PreH4 : (ItemsIncreasing groups_after keys_after )) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_pairs_safety_wit_3 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) = (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition count_pairs_safety_wit_4 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((j - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - i )) ”
.

Definition count_pairs_safety_wit_5 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |->_)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((j - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - i )) ”
.

Definition count_pairs_safety_wit_6 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ”
) \/
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ”
).

Definition count_pairs_safety_wit_6_split_goal_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition count_pairs_safety_wit_6_split_goal_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((INT64_MIN) <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ”
.

Definition count_pairs_safety_wit_7 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((((j - i ) * ((j - i ) - 1 ) ) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_pairs_safety_wit_8 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (((j - i ) * ((j - i ) - 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((j - i ) * ((j - i ) - 1 ) )) ”
.

Definition count_pairs_safety_wit_9 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (((j - i ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((j - i ) - 1 )) ”
.

Definition count_pairs_safety_wit_10 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_pairs_safety_wit_11 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_pairs_safety_wit_12 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ”
) \/
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ”
).

Definition count_pairs_safety_wit_12_split_goal_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition count_pairs_safety_wit_12_split_goal_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((INT64_MIN) <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ”
.

Definition count_pairs_safety_wit_13 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((((j - i ) * ((j - i ) - 1 ) ) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_pairs_safety_wit_14 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (((j - i ) * ((j - i ) - 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((j - i ) * ((j - i ) - 1 ) )) ”
.

Definition count_pairs_safety_wit_15 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (((j - i ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((j - i ) - 1 )) ”
.

Definition count_pairs_safety_wit_16 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_pairs_safety_wit_17 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth j groups_sorted 0) <> (Znth i groups_sorted 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH15 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH16 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH17 : (ValueRunBoundary groups_sorted i )) (PreH18 : (SameValueRange groups_sorted i j )) ,
  ((( &( "g" ) )) # Int64  |-> (j - i ))
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_pairs_safety_wit_18 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q < j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ False ”
.

Definition count_pairs_safety_wit_19 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q < j)) (PreH19 : (q < cnt_pre)) (PreH20 : (g = (j - i ))) (PreH21 : (0 <= total)) (PreH22 : (total <= 45000000000)) (PreH23 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH24 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH25 : (ValueRunBoundary groups_sorted i )) (PreH26 : (ValueRunBoundary groups_sorted j )) (PreH27 : (SameValueRange groups_sorted i j )) (PreH28 : (SameValueRange keys_sorted p q )) (PreH29 : (RangeRunBoundary keys_sorted i j p )) (PreH30 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ False ”
.

Definition count_pairs_safety_wit_20 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) = (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ ((q + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition count_pairs_safety_wit_21 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |->_)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((q - p ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q - p )) ”
.

Definition count_pairs_safety_wit_22 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |->_)
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ ((q - p ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q - p )) ”
.

Definition count_pairs_safety_wit_23 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
) \/
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
).

Definition count_pairs_safety_wit_23_split_goal_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition count_pairs_safety_wit_23_split_goal_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((INT64_MIN) <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
.

Definition count_pairs_safety_wit_24 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ ((((q - p ) * ((q - p ) - 1 ) ) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_pairs_safety_wit_25 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (((q - p ) * ((q - p ) - 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((q - p ) * ((q - p ) - 1 ) )) ”
.

Definition count_pairs_safety_wit_26 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (((q - p ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((q - p ) - 1 )) ”
.

Definition count_pairs_safety_wit_27 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_pairs_safety_wit_28 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH23 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH24 : (ValueRunBoundary groups_sorted i )) (PreH25 : (ValueRunBoundary groups_sorted j )) (PreH26 : (SameValueRange groups_sorted i j )) (PreH27 : (SameValueRange keys_sorted p q )) (PreH28 : (RangeRunBoundary keys_sorted i j p )) (PreH29 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_pairs_safety_wit_29 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
) \/
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
).

Definition count_pairs_safety_wit_29_split_goal_1 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= INT64_MAX) ”
.

Definition count_pairs_safety_wit_29_split_goal_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ ((INT64_MIN) <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
.

Definition count_pairs_safety_wit_30 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ ((((q - p ) * ((q - p ) - 1 ) ) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_pairs_safety_wit_31 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ (((q - p ) * ((q - p ) - 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((q - p ) * ((q - p ) - 1 ) )) ”
.

Definition count_pairs_safety_wit_32 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ (((q - p ) - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((q - p ) - 1 )) ”
.

Definition count_pairs_safety_wit_33 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_pairs_safety_wit_34 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : ((Znth q keys_sorted 0) <> (Znth p keys_sorted 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH25 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH26 : (ValueRunBoundary groups_sorted i )) (PreH27 : (ValueRunBoundary groups_sorted j )) (PreH28 : (SameValueRange groups_sorted i j )) (PreH29 : (SameValueRange keys_sorted p q )) (PreH30 : (RangeRunBoundary keys_sorted i j p )) (PreH31 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  ((( &( "same" ) )) # Int64  |-> (q - p ))
  **  (IntArray.full key_pre cnt_pre keys_sorted )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_pairs_entail_wit_1 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups keys groups_after keys_after )) (PreH4 : (ItemsIncreasing groups_after keys_after )) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) ,
  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (PairCountPrefix groups_sorted keys_sorted 0 0 ) ” 
  &&  “ (ValueRunBoundary groups_sorted 0 ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups keys groups_after keys_after )) (PreH4 : (ItemsIncreasing groups_after keys_after )) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) ,
  TT && emp 
|--
  “ (ValueRunBoundary groups_after 0 ) ” 
  &&  “ (PairCountPrefix groups_after keys_after 0 0 ) ”
  &&  emp
).

Definition count_pairs_entail_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups keys groups_after keys_after )) (PreH4 : (ItemsIncreasing groups_after keys_after )) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) ,
  (ValueRunBoundary groups_after 0 )
.

Definition count_pairs_entail_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (keys_after: (@list Z)) (groups_after: (@list Z)) (PreH1 : ((Zlength (groups_after)) = cnt_pre)) (PreH2 : ((Zlength (keys_after)) = cnt_pre)) (PreH3 : (ParallelPermutation groups keys groups_after keys_after )) (PreH4 : (ItemsIncreasing groups_after keys_after )) (PreH5 : (0 <= cnt_pre)) (PreH6 : (cnt_pre <= cap)) (PreH7 : (cap <= 300000)) (PreH8 : ((Zlength (groups)) = cnt_pre)) (PreH9 : ((Zlength (keys)) = cnt_pre)) ,
  (PairCountPrefix groups_after keys_after 0 0 )
.

Definition count_pairs_entail_wit_2 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (i < cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= cnt_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 45000000000)) (PreH11 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH12 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH13 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH14 : (ValueRunBoundary groups_sorted_2 i )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
  **  (IntArray.full key_pre cnt_pre keys_sorted_2 )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < cnt_pre) ” 
  &&  “ (i <= i) ” 
  &&  “ (i <= cnt_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (PairCountPrefix groups_sorted keys_sorted i total ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (SameValueRange groups_sorted i i ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (i < cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= cnt_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 45000000000)) (PreH11 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH12 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH13 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH14 : (ValueRunBoundary groups_sorted_2 i )) ,
  TT && emp 
|--
  “ (SameValueRange groups_sorted_2 i i ) ”
  &&  emp
).

Definition count_pairs_entail_wit_2_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (i < cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= cnt_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 45000000000)) (PreH11 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH12 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH13 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH14 : (ValueRunBoundary groups_sorted_2 i )) ,
  (SameValueRange groups_sorted_2 i i )
.

Definition count_pairs_entail_wit_3 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) = (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
  **  (IntArray.full key_pre cnt_pre keys_sorted_2 )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < cnt_pre) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= cnt_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (PairCountPrefix groups_sorted keys_sorted i total ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (SameValueRange groups_sorted i (j + 1 ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) = (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  TT && emp 
|--
  “ (SameValueRange groups_sorted_2 i (j + 1 ) ) ”
  &&  emp
).

Definition count_pairs_entail_wit_3_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) = (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (SameValueRange groups_sorted_2 i (j + 1 ) )
.

Definition count_pairs_entail_wit_4_1 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH14 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH15 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH16 : (ValueRunBoundary groups_sorted_2 i )) (PreH17 : (SameValueRange groups_sorted_2 i j )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
  **  (IntArray.full key_pre cnt_pre keys_sorted_2 )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ ((j - i ) = (j - i )) ” 
  &&  “ (0 <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ” 
  &&  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j i ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j i (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH14 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH15 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH16 : (ValueRunBoundary groups_sorted_2 i )) (PreH17 : (SameValueRange groups_sorted_2 i j )) ,
  TT && emp 
|--
  “ (CountGroupPhase groups_sorted_2 keys_sorted_2 i j i (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) ) ” 
  &&  “ (RangeRunBoundary keys_sorted_2 i j i ) ” 
  &&  “ (ValueRunBoundary groups_sorted_2 j ) ” 
  &&  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (0 <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ”
  &&  emp
).

Definition count_pairs_entail_wit_4_1_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH14 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH15 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH16 : (ValueRunBoundary groups_sorted_2 i )) (PreH17 : (SameValueRange groups_sorted_2 i j )) ,
  (CountGroupPhase groups_sorted_2 keys_sorted_2 i j i (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) )
.

Definition count_pairs_entail_wit_4_1_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH14 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH15 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH16 : (ValueRunBoundary groups_sorted_2 i )) (PreH17 : (SameValueRange groups_sorted_2 i j )) ,
  (RangeRunBoundary keys_sorted_2 i j i )
.

Definition count_pairs_entail_wit_4_1_split_goal_3 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH14 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH15 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH16 : (ValueRunBoundary groups_sorted_2 i )) (PreH17 : (SameValueRange groups_sorted_2 i j )) ,
  (ValueRunBoundary groups_sorted_2 j )
.

Definition count_pairs_entail_wit_4_1_split_goal_4 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH14 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH15 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH16 : (ValueRunBoundary groups_sorted_2 i )) (PreH17 : (SameValueRange groups_sorted_2 i j )) ,
  ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= 45000000000)
.

Definition count_pairs_entail_wit_4_1_split_goal_5 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (j >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH14 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH15 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH16 : (ValueRunBoundary groups_sorted_2 i )) (PreH17 : (SameValueRange groups_sorted_2 i j )) ,
  (0 <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ))
.

Definition count_pairs_entail_wit_4_2 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
  **  (IntArray.full key_pre cnt_pre keys_sorted_2 )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ ((j - i ) = (j - i )) ” 
  &&  “ (0 <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ” 
  &&  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j i ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j i (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  TT && emp 
|--
  “ (CountGroupPhase groups_sorted_2 keys_sorted_2 i j i (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) ) ” 
  &&  “ (RangeRunBoundary keys_sorted_2 i j i ) ” 
  &&  “ (ValueRunBoundary groups_sorted_2 j ) ” 
  &&  “ ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (0 <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) )) ” 
  &&  “ (i < j) ”
  &&  emp
).

Definition count_pairs_entail_wit_4_2_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (CountGroupPhase groups_sorted_2 keys_sorted_2 i j i (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) )
.

Definition count_pairs_entail_wit_4_2_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (RangeRunBoundary keys_sorted_2 i j i )
.

Definition count_pairs_entail_wit_4_2_split_goal_3 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (ValueRunBoundary groups_sorted_2 j )
.

Definition count_pairs_entail_wit_4_2_split_goal_4 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  ((total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ) <= 45000000000)
.

Definition count_pairs_entail_wit_4_2_split_goal_5 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (0 <= (total + (((j - i ) * ((j - i ) - 1 ) ) ÷ 2 ) ))
.

Definition count_pairs_entail_wit_4_2_split_goal_6 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth j groups_sorted_2 0) <> (Znth i groups_sorted_2 0))) (PreH2 : (j < cnt_pre)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < cnt_pre)) (PreH10 : (i <= j)) (PreH11 : (j <= cnt_pre)) (PreH12 : (0 <= total)) (PreH13 : (total <= 45000000000)) (PreH14 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH15 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH16 : (PairCountPrefix groups_sorted_2 keys_sorted_2 i total )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (SameValueRange groups_sorted_2 i j )) ,
  (i < j)
.

Definition count_pairs_entail_wit_5 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total_3: Z) (g_3: Z) (p_3: Z) (j_3: Z) (i_3: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (p_3 < j_3)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i_3)) (PreH8 : (i_3 < j_3)) (PreH9 : (j_3 <= cnt_pre)) (PreH10 : (i_3 <= p_3)) (PreH11 : (p_3 <= j_3)) (PreH12 : (g_3 = (j_3 - i_3 ))) (PreH13 : (0 <= total_3)) (PreH14 : (total_3 <= 45000000000)) (PreH15 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH16 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH17 : (ValueRunBoundary groups_sorted_2 i_3 )) (PreH18 : (ValueRunBoundary groups_sorted_2 j_3 )) (PreH19 : (SameValueRange groups_sorted_2 i_3 j_3 )) (PreH20 : (RangeRunBoundary keys_sorted_2 i_3 j_3 p_3 )) (PreH21 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i_3 j_3 p_3 total_3 )) ,
  ((( &( "q" ) )) # Int  |-> p_3)
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i_3)
  **  ((( &( "j" ) )) # Int  |-> j_3)
  **  ((( &( "p" ) )) # Int  |-> p_3)
  **  ((( &( "g" ) )) # Int64  |-> g_3)
  **  ((( &( "total" ) )) # Int64  |-> total_3)
  **  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
  **  (IntArray.full key_pre cnt_pre keys_sorted_2 )
|--
  (EX (total: Z)  (g: Z)  (q: Z)  (p: Z)  (j: Z)  (i: Z)  (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= p) ” 
  &&  “ (p < j) ” 
  &&  “ (p <= q) ” 
  &&  “ (q <= j) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < cnt_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= cnt_pre) ” 
  &&  “ (q = j) ” 
  &&  “ (g = (j - i )) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (SameValueRange keys_sorted p q ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j p ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j p total ) ”
  &&  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted ))
  ||
  (EX (total_2: Z)  (g_2: Z)  (q_2: Z)  (p_2: Z)  (j_2: Z)  (i_2: Z)  (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < j_2) ” 
  &&  “ (j_2 <= cnt_pre) ” 
  &&  “ (i_2 <= p_2) ” 
  &&  “ (p_2 < j_2) ” 
  &&  “ (p_2 <= q_2) ” 
  &&  “ (q_2 <= j_2) ” 
  &&  “ (0 <= p_2) ” 
  &&  “ (p_2 < cnt_pre) ” 
  &&  “ (0 <= q_2) ” 
  &&  “ (q_2 <= cnt_pre) ” 
  &&  “ (q_2 < j_2) ” 
  &&  “ (q_2 < cnt_pre) ” 
  &&  “ (g_2 = (j_2 - i_2 )) ” 
  &&  “ (0 <= total_2) ” 
  &&  “ (total_2 <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i_2 ) ” 
  &&  “ (ValueRunBoundary groups_sorted j_2 ) ” 
  &&  “ (SameValueRange groups_sorted i_2 j_2 ) ” 
  &&  “ (SameValueRange keys_sorted p_2 q_2 ) ” 
  &&  “ (RangeRunBoundary keys_sorted i_2 j_2 p_2 ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i_2 j_2 p_2 total_2 ) ”
  &&  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  ((( &( "p" ) )) # Int  |-> p_2)
  **  ((( &( "q" ) )) # Int  |-> q_2)
  **  ((( &( "g" ) )) # Int64  |-> g_2)
  **  ((( &( "total" ) )) # Int64  |-> total_2)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted ))
.

Definition count_pairs_entail_wit_6 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total_3: Z) (g_3: Z) (q_3: Z) (p_3: Z) (j_3: Z) (i_3: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth q_3 keys_sorted_2 0) = (Znth p_3 keys_sorted_2 0))) (PreH2 : (q_3 < j_3)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i_3)) (PreH9 : (i_3 < j_3)) (PreH10 : (j_3 <= cnt_pre)) (PreH11 : (i_3 <= p_3)) (PreH12 : (p_3 < j_3)) (PreH13 : (p_3 <= q_3)) (PreH14 : (q_3 <= j_3)) (PreH15 : (0 <= p_3)) (PreH16 : (p_3 < cnt_pre)) (PreH17 : (0 <= q_3)) (PreH18 : (q_3 <= cnt_pre)) (PreH19 : (q_3 < j_3)) (PreH20 : (q_3 < cnt_pre)) (PreH21 : (g_3 = (j_3 - i_3 ))) (PreH22 : (0 <= total_3)) (PreH23 : (total_3 <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH25 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH26 : (ValueRunBoundary groups_sorted_2 i_3 )) (PreH27 : (ValueRunBoundary groups_sorted_2 j_3 )) (PreH28 : (SameValueRange groups_sorted_2 i_3 j_3 )) (PreH29 : (SameValueRange keys_sorted_2 p_3 q_3 )) (PreH30 : (RangeRunBoundary keys_sorted_2 i_3 j_3 p_3 )) (PreH31 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i_3 j_3 p_3 total_3 )) ,
  (IntArray.full key_pre cnt_pre keys_sorted_2 )
  **  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i_3)
  **  ((( &( "j" ) )) # Int  |-> j_3)
  **  ((( &( "p" ) )) # Int  |-> p_3)
  **  ((( &( "q" ) )) # Int  |-> (q_3 + 1 ))
  **  ((( &( "g" ) )) # Int64  |-> g_3)
  **  ((( &( "total" ) )) # Int64  |-> total_3)
  **  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
|--
  (EX (total: Z)  (g: Z)  (q: Z)  (p: Z)  (j: Z)  (i: Z)  (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= p) ” 
  &&  “ (p < j) ” 
  &&  “ (p <= q) ” 
  &&  “ (q <= j) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < cnt_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= cnt_pre) ” 
  &&  “ (q = j) ” 
  &&  “ (g = (j - i )) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (SameValueRange keys_sorted p q ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j p ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j p total ) ”
  &&  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "g" ) )) # Int64  |-> g)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted ))
  ||
  (EX (total_2: Z)  (g_2: Z)  (q_2: Z)  (p_2: Z)  (j_2: Z)  (i_2: Z)  (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < j_2) ” 
  &&  “ (j_2 <= cnt_pre) ” 
  &&  “ (i_2 <= p_2) ” 
  &&  “ (p_2 < j_2) ” 
  &&  “ (p_2 <= q_2) ” 
  &&  “ (q_2 <= j_2) ” 
  &&  “ (0 <= p_2) ” 
  &&  “ (p_2 < cnt_pre) ” 
  &&  “ (0 <= q_2) ” 
  &&  “ (q_2 <= cnt_pre) ” 
  &&  “ (q_2 < j_2) ” 
  &&  “ (q_2 < cnt_pre) ” 
  &&  “ (g_2 = (j_2 - i_2 )) ” 
  &&  “ (0 <= total_2) ” 
  &&  “ (total_2 <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i_2 ) ” 
  &&  “ (ValueRunBoundary groups_sorted j_2 ) ” 
  &&  “ (SameValueRange groups_sorted i_2 j_2 ) ” 
  &&  “ (SameValueRange keys_sorted p_2 q_2 ) ” 
  &&  “ (RangeRunBoundary keys_sorted i_2 j_2 p_2 ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i_2 j_2 p_2 total_2 ) ”
  &&  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  ((( &( "p" ) )) # Int  |-> p_2)
  **  ((( &( "q" ) )) # Int  |-> q_2)
  **  ((( &( "g" ) )) # Int64  |-> g_2)
  **  ((( &( "total" ) )) # Int64  |-> total_2)
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted ))
.

Definition count_pairs_entail_wit_7_1 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH23 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH24 : (ValueRunBoundary groups_sorted_2 i )) (PreH25 : (ValueRunBoundary groups_sorted_2 j )) (PreH26 : (SameValueRange groups_sorted_2 i j )) (PreH27 : (SameValueRange keys_sorted_2 p q )) (PreH28 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH29 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
  **  (IntArray.full key_pre cnt_pre keys_sorted_2 )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= q) ” 
  &&  “ (q <= j) ” 
  &&  “ (g = (j - i )) ” 
  &&  “ (0 <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ” 
  &&  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j q ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j q (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH23 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH24 : (ValueRunBoundary groups_sorted_2 i )) (PreH25 : (ValueRunBoundary groups_sorted_2 j )) (PreH26 : (SameValueRange groups_sorted_2 i j )) (PreH27 : (SameValueRange keys_sorted_2 p q )) (PreH28 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH29 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  TT && emp 
|--
  “ (CountGroupPhase groups_sorted_2 keys_sorted_2 i q q (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) ) ” 
  &&  “ (RangeRunBoundary keys_sorted_2 i q q ) ” 
  &&  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (0 <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
  &&  emp
).

Definition count_pairs_entail_wit_7_1_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH23 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH24 : (ValueRunBoundary groups_sorted_2 i )) (PreH25 : (ValueRunBoundary groups_sorted_2 j )) (PreH26 : (SameValueRange groups_sorted_2 i j )) (PreH27 : (SameValueRange keys_sorted_2 p q )) (PreH28 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH29 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (CountGroupPhase groups_sorted_2 keys_sorted_2 i q q (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) )
.

Definition count_pairs_entail_wit_7_1_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH23 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH24 : (ValueRunBoundary groups_sorted_2 i )) (PreH25 : (ValueRunBoundary groups_sorted_2 j )) (PreH26 : (SameValueRange groups_sorted_2 i j )) (PreH27 : (SameValueRange keys_sorted_2 p q )) (PreH28 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH29 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (RangeRunBoundary keys_sorted_2 i q q )
.

Definition count_pairs_entail_wit_7_1_split_goal_3 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH23 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH24 : (ValueRunBoundary groups_sorted_2 i )) (PreH25 : (ValueRunBoundary groups_sorted_2 j )) (PreH26 : (SameValueRange groups_sorted_2 i j )) (PreH27 : (SameValueRange keys_sorted_2 p q )) (PreH28 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH29 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= 45000000000)
.

Definition count_pairs_entail_wit_7_1_split_goal_4 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (q >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q = j)) (PreH19 : (g = (j - i ))) (PreH20 : (0 <= total)) (PreH21 : (total <= 45000000000)) (PreH22 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH23 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH24 : (ValueRunBoundary groups_sorted_2 i )) (PreH25 : (ValueRunBoundary groups_sorted_2 j )) (PreH26 : (SameValueRange groups_sorted_2 i j )) (PreH27 : (SameValueRange keys_sorted_2 p q )) (PreH28 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH29 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (0 <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ))
.

Definition count_pairs_entail_wit_7_2 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth q keys_sorted_2 0) <> (Znth p keys_sorted_2 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH25 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH26 : (ValueRunBoundary groups_sorted_2 i )) (PreH27 : (ValueRunBoundary groups_sorted_2 j )) (PreH28 : (SameValueRange groups_sorted_2 i j )) (PreH29 : (SameValueRange keys_sorted_2 p q )) (PreH30 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH31 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (IntArray.full key_pre cnt_pre keys_sorted_2 )
  **  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= q) ” 
  &&  “ (q <= j) ” 
  &&  “ (g = (j - i )) ” 
  &&  “ (0 <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ” 
  &&  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j q ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j q (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth q keys_sorted_2 0) <> (Znth p keys_sorted_2 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH25 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH26 : (ValueRunBoundary groups_sorted_2 i )) (PreH27 : (ValueRunBoundary groups_sorted_2 j )) (PreH28 : (SameValueRange groups_sorted_2 i j )) (PreH29 : (SameValueRange keys_sorted_2 p q )) (PreH30 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH31 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  TT && emp 
|--
  “ (CountGroupPhase groups_sorted_2 keys_sorted_2 i j q (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) ) ” 
  &&  “ (RangeRunBoundary keys_sorted_2 i j q ) ” 
  &&  “ ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= 45000000000) ” 
  &&  “ (0 <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) )) ”
  &&  emp
).

Definition count_pairs_entail_wit_7_2_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth q keys_sorted_2 0) <> (Znth p keys_sorted_2 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH25 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH26 : (ValueRunBoundary groups_sorted_2 i )) (PreH27 : (ValueRunBoundary groups_sorted_2 j )) (PreH28 : (SameValueRange groups_sorted_2 i j )) (PreH29 : (SameValueRange keys_sorted_2 p q )) (PreH30 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH31 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (CountGroupPhase groups_sorted_2 keys_sorted_2 i j q (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) )
.

Definition count_pairs_entail_wit_7_2_split_goal_2 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth q keys_sorted_2 0) <> (Znth p keys_sorted_2 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH25 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH26 : (ValueRunBoundary groups_sorted_2 i )) (PreH27 : (ValueRunBoundary groups_sorted_2 j )) (PreH28 : (SameValueRange groups_sorted_2 i j )) (PreH29 : (SameValueRange keys_sorted_2 p q )) (PreH30 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH31 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (RangeRunBoundary keys_sorted_2 i j q )
.

Definition count_pairs_entail_wit_7_2_split_goal_3 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth q keys_sorted_2 0) <> (Znth p keys_sorted_2 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH25 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH26 : (ValueRunBoundary groups_sorted_2 i )) (PreH27 : (ValueRunBoundary groups_sorted_2 j )) (PreH28 : (SameValueRange groups_sorted_2 i j )) (PreH29 : (SameValueRange keys_sorted_2 p q )) (PreH30 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH31 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  ((total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ) <= 45000000000)
.

Definition count_pairs_entail_wit_7_2_split_goal_4 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : ((Znth q keys_sorted_2 0) <> (Znth p keys_sorted_2 0))) (PreH2 : (q < j)) (PreH3 : (0 <= cnt_pre)) (PreH4 : (cnt_pre <= cap)) (PreH5 : (cap <= 300000)) (PreH6 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH7 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (i <= p)) (PreH12 : (p < j)) (PreH13 : (p <= q)) (PreH14 : (q <= j)) (PreH15 : (0 <= p)) (PreH16 : (p < cnt_pre)) (PreH17 : (0 <= q)) (PreH18 : (q <= cnt_pre)) (PreH19 : (q < j)) (PreH20 : (q < cnt_pre)) (PreH21 : (g = (j - i ))) (PreH22 : (0 <= total)) (PreH23 : (total <= 45000000000)) (PreH24 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH25 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH26 : (ValueRunBoundary groups_sorted_2 i )) (PreH27 : (ValueRunBoundary groups_sorted_2 j )) (PreH28 : (SameValueRange groups_sorted_2 i j )) (PreH29 : (SameValueRange keys_sorted_2 p q )) (PreH30 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH31 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (0 <= (total - (((q - p ) * ((q - p ) - 1 ) ) ÷ 2 ) ))
.

Definition count_pairs_entail_wit_8 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (p >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p <= j)) (PreH12 : (g = (j - i ))) (PreH13 : (0 <= total)) (PreH14 : (total <= 45000000000)) (PreH15 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH16 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (ValueRunBoundary groups_sorted_2 j )) (PreH19 : (SameValueRange groups_sorted_2 i j )) (PreH20 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH21 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted_2 )
  **  (IntArray.full key_pre cnt_pre keys_sorted_2 )
|--
  EX (keys_sorted: (@list Z))  (groups_sorted: (@list Z)) ,
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (PairCountPrefix groups_sorted keys_sorted j total ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (p >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p <= j)) (PreH12 : (g = (j - i ))) (PreH13 : (0 <= total)) (PreH14 : (total <= 45000000000)) (PreH15 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH16 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (ValueRunBoundary groups_sorted_2 j )) (PreH19 : (SameValueRange groups_sorted_2 i j )) (PreH20 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH21 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  TT && emp 
|--
  “ (PairCountPrefix groups_sorted_2 keys_sorted_2 j total ) ”
  &&  emp
).

Definition count_pairs_entail_wit_8_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (p: Z) (j: Z) (i: Z) (keys_sorted_2: (@list Z)) (groups_sorted_2: (@list Z)) (PreH1 : (p >= j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted_2)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted_2)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p <= j)) (PreH12 : (g = (j - i ))) (PreH13 : (0 <= total)) (PreH14 : (total <= 45000000000)) (PreH15 : (ParallelPermutation groups keys groups_sorted_2 keys_sorted_2 )) (PreH16 : (ItemsIncreasing groups_sorted_2 keys_sorted_2 )) (PreH17 : (ValueRunBoundary groups_sorted_2 i )) (PreH18 : (ValueRunBoundary groups_sorted_2 j )) (PreH19 : (SameValueRange groups_sorted_2 i j )) (PreH20 : (RangeRunBoundary keys_sorted_2 i j p )) (PreH21 : (CountGroupPhase groups_sorted_2 keys_sorted_2 i j p total )) ,
  (PairCountPrefix groups_sorted_2 keys_sorted_2 j total )
.

Definition count_pairs_return_wit_1 := 
(
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (i >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= cnt_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 45000000000)) (PreH11 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH12 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH13 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH14 : (ValueRunBoundary groups_sorted i )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  EX (keys_after: (@list Z))  (groups_after: (@list Z)) ,
  “ ((Zlength (groups_after)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_after)) = cnt_pre) ” 
  &&  “ (ParallelPermutation groups keys groups_after keys_after ) ” 
  &&  “ (PairCountPrefix groups keys cnt_pre total ) ”
  &&  (IntArray.full grp_pre cnt_pre groups_after )
  **  (IntArray.full key_pre cnt_pre keys_after )
) \/
(
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (i >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= cnt_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 45000000000)) (PreH11 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH12 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH13 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH14 : (ValueRunBoundary groups_sorted i )) ,
  TT && emp 
|--
  “ (PairCountPrefix groups keys cnt_pre total ) ”
  &&  emp
).

Definition count_pairs_return_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (i >= cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= cnt_pre)) (PreH9 : (0 <= total)) (PreH10 : (total <= 45000000000)) (PreH11 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH12 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH13 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH14 : (ValueRunBoundary groups_sorted i )) ,
  (PairCountPrefix groups keys cnt_pre total )
.

Definition count_pairs_partial_solve_wit_1_pure := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  ((( &( "grp" ) )) # Ptr  |-> grp_pre)
  **  ((( &( "key" ) )) # Ptr  |-> key_pre)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_pre)
  **  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ”
.

Definition count_pairs_partial_solve_wit_1_aux := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (PreH1 : (0 <= cnt_pre)) (PreH2 : (cnt_pre <= cap)) (PreH3 : (cap <= 300000)) (PreH4 : ((Zlength (groups)) = cnt_pre)) (PreH5 : ((Zlength (keys)) = cnt_pre)) ,
  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
|--
  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups)) = cnt_pre) ” 
  &&  “ ((Zlength (keys)) = cnt_pre) ”
  &&  (IntArray.full grp_pre cnt_pre groups )
  **  (IntArray.full key_pre cnt_pre keys )
.

Definition count_pairs_partial_solve_wit_1 := count_pairs_partial_solve_wit_1_pure -> count_pairs_partial_solve_wit_1_aux.

Definition count_pairs_partial_solve_wit_2 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j < cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (j < cnt_pre) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < cnt_pre) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (PairCountPrefix groups_sorted keys_sorted i total ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ”
  &&  (((grp_pre + (j * sizeof(INT)))) # Int  |-> (Znth j groups_sorted 0))
  **  (IntArray.missing_i grp_pre j 0 cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
.

Definition count_pairs_partial_solve_wit_3 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (j < cnt_pre)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < cnt_pre)) (PreH9 : (i <= j)) (PreH10 : (j <= cnt_pre)) (PreH11 : (0 <= total)) (PreH12 : (total <= 45000000000)) (PreH13 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH14 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH15 : (PairCountPrefix groups_sorted keys_sorted i total )) (PreH16 : (ValueRunBoundary groups_sorted i )) (PreH17 : (SameValueRange groups_sorted i j )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (j < cnt_pre) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < cnt_pre) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (PairCountPrefix groups_sorted keys_sorted i total ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ”
  &&  (((grp_pre + (i * sizeof(INT)))) # Int  |-> (Znth i groups_sorted 0))
  **  (IntArray.missing_i grp_pre i 0 cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
.

Definition count_pairs_partial_solve_wit_4 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q < j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q < j)) (PreH19 : (q < cnt_pre)) (PreH20 : (g = (j - i ))) (PreH21 : (0 <= total)) (PreH22 : (total <= 45000000000)) (PreH23 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH24 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH25 : (ValueRunBoundary groups_sorted i )) (PreH26 : (ValueRunBoundary groups_sorted j )) (PreH27 : (SameValueRange groups_sorted i j )) (PreH28 : (SameValueRange keys_sorted p q )) (PreH29 : (RangeRunBoundary keys_sorted i j p )) (PreH30 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  (IntArray.full grp_pre cnt_pre groups_sorted )
  **  (IntArray.full key_pre cnt_pre keys_sorted )
|--
  “ (q < j) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= p) ” 
  &&  “ (p < j) ” 
  &&  “ (p <= q) ” 
  &&  “ (q <= j) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < cnt_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= cnt_pre) ” 
  &&  “ (q < j) ” 
  &&  “ (q < cnt_pre) ” 
  &&  “ (g = (j - i )) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (SameValueRange keys_sorted p q ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j p ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j p total ) ”
  &&  (((key_pre + (q * sizeof(INT)))) # Int  |-> (Znth q keys_sorted 0))
  **  (IntArray.missing_i key_pre q 0 cnt_pre keys_sorted )
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
.

Definition count_pairs_partial_solve_wit_5 := 
forall (cnt_pre: Z) (key_pre: Z) (grp_pre: Z) (cap: Z) (keys: (@list Z)) (groups: (@list Z)) (total: Z) (g: Z) (q: Z) (p: Z) (j: Z) (i: Z) (keys_sorted: (@list Z)) (groups_sorted: (@list Z)) (PreH1 : (q < j)) (PreH2 : (0 <= cnt_pre)) (PreH3 : (cnt_pre <= cap)) (PreH4 : (cap <= 300000)) (PreH5 : ((Zlength (groups_sorted)) = cnt_pre)) (PreH6 : ((Zlength (keys_sorted)) = cnt_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < j)) (PreH9 : (j <= cnt_pre)) (PreH10 : (i <= p)) (PreH11 : (p < j)) (PreH12 : (p <= q)) (PreH13 : (q <= j)) (PreH14 : (0 <= p)) (PreH15 : (p < cnt_pre)) (PreH16 : (0 <= q)) (PreH17 : (q <= cnt_pre)) (PreH18 : (q < j)) (PreH19 : (q < cnt_pre)) (PreH20 : (g = (j - i ))) (PreH21 : (0 <= total)) (PreH22 : (total <= 45000000000)) (PreH23 : (ParallelPermutation groups keys groups_sorted keys_sorted )) (PreH24 : (ItemsIncreasing groups_sorted keys_sorted )) (PreH25 : (ValueRunBoundary groups_sorted i )) (PreH26 : (ValueRunBoundary groups_sorted j )) (PreH27 : (SameValueRange groups_sorted i j )) (PreH28 : (SameValueRange keys_sorted p q )) (PreH29 : (RangeRunBoundary keys_sorted i j p )) (PreH30 : (CountGroupPhase groups_sorted keys_sorted i j p total )) ,
  (IntArray.full key_pre cnt_pre keys_sorted )
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
|--
  “ (q < j) ” 
  &&  “ (0 <= cnt_pre) ” 
  &&  “ (cnt_pre <= cap) ” 
  &&  “ (cap <= 300000) ” 
  &&  “ ((Zlength (groups_sorted)) = cnt_pre) ” 
  &&  “ ((Zlength (keys_sorted)) = cnt_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= cnt_pre) ” 
  &&  “ (i <= p) ” 
  &&  “ (p < j) ” 
  &&  “ (p <= q) ” 
  &&  “ (q <= j) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < cnt_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= cnt_pre) ” 
  &&  “ (q < j) ” 
  &&  “ (q < cnt_pre) ” 
  &&  “ (g = (j - i )) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 45000000000) ” 
  &&  “ (ParallelPermutation groups keys groups_sorted keys_sorted ) ” 
  &&  “ (ItemsIncreasing groups_sorted keys_sorted ) ” 
  &&  “ (ValueRunBoundary groups_sorted i ) ” 
  &&  “ (ValueRunBoundary groups_sorted j ) ” 
  &&  “ (SameValueRange groups_sorted i j ) ” 
  &&  “ (SameValueRange keys_sorted p q ) ” 
  &&  “ (RangeRunBoundary keys_sorted i j p ) ” 
  &&  “ (CountGroupPhase groups_sorted keys_sorted i j p total ) ”
  &&  (((key_pre + (p * sizeof(INT)))) # Int  |-> (Znth p keys_sorted 0))
  **  (IntArray.missing_i key_pre p 0 cnt_pre keys_sorted )
  **  (IntArray.full grp_pre cnt_pre groups_sorted )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z))  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_lines 0)) /\ ((Znth i x_lines 0) <= 1000000)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_lines 0)) /\ ((Znth i_2 y_lines 0) <= 1000000)))) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < k_pre)) -> ((((0 <= (fst ((Znth i_3 people __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)) /\ (0 <= (snd ((Znth i_3 people __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)))) (PreH10 : (Pre x_lines y_lines people )) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < k_pre)) -> (((Znth i_4 person_x 0) = (fst ((Znth i_4 people __default__Prod_Z_Z)))) /\ ((Znth i_4 person_y 0) = (snd ((Znth i_4 people __default__Prod_Z_Z))))))) ,
  ((( &( "nh" ) )) # Int  |->_)
  **  ((( &( "nv" ) )) # Int  |-> 0)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z))  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_lines 0)) /\ ((Znth i x_lines 0) <= 1000000)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_lines 0)) /\ ((Znth i_2 y_lines 0) <= 1000000)))) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < k_pre)) -> ((((0 <= (fst ((Znth i_3 people __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)) /\ (0 <= (snd ((Znth i_3 people __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)))) (PreH10 : (Pre x_lines y_lines people )) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < k_pre)) -> (((Znth i_4 person_x 0) = (fst ((Znth i_4 people __default__Prod_Z_Z)))) /\ ((Znth i_4 person_y 0) = (snd ((Znth i_4 people __default__Prod_Z_Z))))))) ,
  ((( &( "nv" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z))  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_lines 0)) /\ ((Znth i x_lines 0) <= 1000000)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_lines 0)) /\ ((Znth i_2 y_lines 0) <= 1000000)))) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < k_pre)) -> ((((0 <= (fst ((Znth i_3 people __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)) /\ (0 <= (snd ((Znth i_3 people __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)))) (PreH10 : (Pre x_lines y_lines people )) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < k_pre)) -> (((Znth i_4 person_x 0) = (fst ((Znth i_4 people __default__Prod_Z_Z)))) /\ ((Znth i_4 person_y 0) = (snd ((Znth i_4 people __default__Prod_Z_Z))))))) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "nh" ) )) # Int  |-> 0)
  **  ((( &( "nv" ) )) # Int  |-> 0)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH2 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH3 : (p < k_pre)) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (2 <= m_pre)) (PreH7 : (m_pre <= 200000)) (PreH8 : (2 <= k_pre)) (PreH9 : (k_pre <= 300000)) (PreH10 : (n_pre = (Zlength (x_lines)))) (PreH11 : (m_pre = (Zlength (y_lines)))) (PreH12 : (k_pre = (Zlength (people)))) (PreH13 : ((Zlength (person_x)) = k_pre)) (PreH14 : ((Zlength (person_y)) = k_pre)) (PreH15 : (Pre x_lines y_lines people )) (PreH16 : (StreetCoordinateBounds x_lines )) (PreH17 : (StreetCoordinateBounds y_lines )) (PreH18 : (PeopleCoordinateBounds people )) (PreH19 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH20 : (0 <= p)) (PreH21 : (p <= k_pre)) (PreH22 : (0 <= nv)) (PreH23 : (nv <= p)) (PreH24 : (0 <= nh)) (PreH25 : (nh <= p)) (PreH26 : ((Zlength (vg)) = nv)) (PreH27 : ((Zlength (vk)) = nv)) (PreH28 : ((Zlength (hg)) = nh)) (PreH29 : ((Zlength (hk)) = nh)) (PreH30 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH33 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH34 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH35 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |-> retval_2)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval >= 0)) (PreH2 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH3 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH4 : (p < k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH21 : (0 <= p)) (PreH22 : (p <= k_pre)) (PreH23 : (0 <= nv)) (PreH24 : (nv <= p)) (PreH25 : (0 <= nh)) (PreH26 : (nh <= p)) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.seg va_key_pre nv k_pre (replace_Znth ((nv - nv )) ((Znth p person_x 0)) (vk_tail)) )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.seg va_grp_pre nv k_pre (replace_Znth ((nv - nv )) (retval) (vg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  ((( &( "sx" ) )) # Int  |-> retval_2)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((nv + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nv + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval < 0)) (PreH2 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH3 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH4 : (p < k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH21 : (0 <= p)) (PreH22 : (p <= k_pre)) (PreH23 : (0 <= nv)) (PreH24 : (nv <= p)) (PreH25 : (0 <= nh)) (PreH26 : (nh <= p)) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |-> retval_2)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 >= 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg)) = nv)) (PreH29 : ((Zlength (vk)) = nv)) (PreH30 : ((Zlength (hg)) = nh)) (PreH31 : ((Zlength (hk)) = nh)) (PreH32 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.seg ha_key_pre nh k_pre (replace_Znth ((nh - nh )) ((Znth p person_y 0)) (hk_tail)) )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg ha_grp_pre nh k_pre (replace_Znth ((nh - nh )) (retval_2) (hg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |-> retval_2)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.full ha_key_pre nh hk )
|--
  “ ((nh + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (nh + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) (PreH35 : (0 <= sy)) (PreH36 : (vg_next = (app (vg) ((cons (sy) ((@nil Z))))))) (PreH37 : (vk_next = (app (vk) ((cons ((Znth p person_x 0)) ((@nil Z))))))) (PreH38 : (hg_next = hg)) (PreH39 : (hk_next = hk)) (PreH40 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH41 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) (PreH35 : (sy < 0)) (PreH36 : (0 <= sx)) (PreH37 : (vg_next = vg)) (PreH38 : (vk_next = vk)) (PreH39 : (hg_next = (app (hg) ((cons (sx) ((@nil Z))))))) (PreH40 : (hk_next = (app (hk) ((cons ((Znth p person_y 0)) ((@nil Z))))))) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) (PreH35 : (sy < 0)) (PreH36 : (sx < 0)) (PreH37 : (vg_next = vg)) (PreH38 : (vk_next = vk)) (PreH39 : (hg_next = hg)) (PreH40 : (hk_next = hk)) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_11 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
).

Definition solver_safety_wit_11_split_goal_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z))  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_lines 0)) /\ ((Znth i x_lines 0) <= 1000000)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_lines 0)) /\ ((Znth i_2 y_lines 0) <= 1000000)))) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < k_pre)) -> ((((0 <= (fst ((Znth i_3 people __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)) /\ (0 <= (snd ((Znth i_3 people __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)))) (PreH10 : (Pre x_lines y_lines people )) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < k_pre)) -> (((Znth i_4 person_x 0) = (fst ((Znth i_4 people __default__Prod_Z_Z)))) /\ ((Znth i_4 person_y 0) = (snd ((Znth i_4 people __default__Prod_Z_Z))))))) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
|--
  EX (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk: (@list Z))  (hg: (@list Z))  (vk: (@list Z))  (vg: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (vg)) = 0) ” 
  &&  “ ((Zlength (vk)) = 0) ” 
  &&  “ ((Zlength (hg)) = 0) ” 
  &&  “ ((Zlength (hk)) = 0) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - 0 )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - 0 )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - 0 )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - 0 )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people 0 vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people 0 vg vk hg hk ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre 0 vg )
  **  (IntArray.seg va_grp_pre 0 k_pre vg_tail )
  **  (IntArray.full va_key_pre 0 vk )
  **  (IntArray.seg va_key_pre 0 k_pre vk_tail )
  **  (IntArray.full ha_grp_pre 0 hg )
  **  (IntArray.seg ha_grp_pre 0 k_pre hg_tail )
  **  (IntArray.full ha_key_pre 0 hk )
  **  (IntArray.seg ha_key_pre 0 k_pre hk_tail )
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z))  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i x_lines 0)) /\ ((Znth i x_lines 0) <= 1000000)))) (PreH8 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < m_pre)) -> ((0 <= (Znth i_2 y_lines 0)) /\ ((Znth i_2 y_lines 0) <= 1000000)))) (PreH9 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < k_pre)) -> ((((0 <= (fst ((Znth i_3 people __default__Prod_Z_Z)))) /\ ((fst ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)) /\ (0 <= (snd ((Znth i_3 people __default__Prod_Z_Z))))) /\ ((snd ((Znth i_3 people __default__Prod_Z_Z))) <= 1000000)))) (PreH10 : (Pre x_lines y_lines people )) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : forall (i_4: Z) , (((0 <= i_4) /\ (i_4 < k_pre)) -> (((Znth i_4 person_x 0) = (fst ((Znth i_4 people __default__Prod_Z_Z)))) /\ ((Znth i_4 person_y 0) = (snd ((Znth i_4 people __default__Prod_Z_Z))))))) ,
  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
|--
  EX (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - 0 )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - 0 )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - 0 )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - 0 )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people 0 (@nil Z) (@nil Z) (@nil Z) (@nil Z) ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people 0 (@nil Z) (@nil Z) (@nil Z) (@nil Z) ) ”
  &&  (IntArray.seg va_grp_pre 0 k_pre vg_tail )
  **  (IntArray.seg va_key_pre 0 k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre 0 k_pre hg_tail )
  **  (IntArray.seg ha_key_pre 0 k_pre hk_tail )
).

Definition solver_entail_wit_2_1 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval >= 0)) (PreH2 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH3 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH4 : (p < k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH21 : (0 <= p)) (PreH22 : (p <= k_pre)) (PreH23 : (0 <= nv)) (PreH24 : (nv <= p)) (PreH25 : (0 <= nh)) (PreH26 : (nh <= p)) (PreH27 : ((Zlength (vg_2)) = nv)) (PreH28 : ((Zlength (vk_2)) = nv)) (PreH29 : ((Zlength (hg_2)) = nh)) (PreH30 : ((Zlength (hk_2)) = nh)) (PreH31 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (IntArray.seg va_key_pre nv k_pre (replace_Znth ((nv - nv )) ((Znth p person_x 0)) (vk_tail_2)) )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.seg va_grp_pre nv k_pre (replace_Znth ((nv - nv )) (retval) (vg_tail_2)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_2 )
  **  (IntArray.full va_key_pre nv vk_2 )
  **  (IntArray.full ha_grp_pre nh hg_2 )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail_2 )
  **  (IntArray.full ha_key_pre nh hk_2 )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail_2 )
|--
  EX (vg: (@list Z))  (vk: (@list Z))  (hg: (@list Z))  (hk: (@list Z))  (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk_next: (@list Z))  (hg_next: (@list Z))  (vk_next: (@list Z))  (vg_next: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (0 <= (nv + 1 )) ” 
  &&  “ ((nv + 1 ) <= (p + 1 )) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= (p + 1 )) ” 
  &&  “ ((Zlength (vg_next)) = (nv + 1 )) ” 
  &&  “ ((Zlength (vk_next)) = (nv + 1 )) ” 
  &&  “ ((Zlength (hg_next)) = nh) ” 
  &&  “ ((Zlength (hk_next)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - (nv + 1 ) )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - (nv + 1 ) )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (vg_next = (app (vg) ((cons (retval) ((@nil Z)))))) ” 
  &&  “ (vk_next = (app (vk) ((cons ((Znth p person_x 0)) ((@nil Z)))))) ” 
  &&  “ (hg_next = hg) ” 
  &&  “ (hk_next = hk) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre (nv + 1 ) vg_next )
  **  (IntArray.seg va_grp_pre (nv + 1 ) k_pre vg_tail )
  **  (IntArray.full va_key_pre (nv + 1 ) vk_next )
  **  (IntArray.seg va_key_pre (nv + 1 ) k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
) \/
(
forall (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval >= 0)) (PreH2 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH3 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH4 : (p < k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH21 : (0 <= p)) (PreH22 : (p <= k_pre)) (PreH23 : (0 <= nv)) (PreH24 : (nv <= p)) (PreH25 : (0 <= nh)) (PreH26 : (nh <= p)) (PreH27 : ((Zlength (vg_2)) = nv)) (PreH28 : ((Zlength (vk_2)) = nv)) (PreH29 : ((Zlength (hg_2)) = nh)) (PreH30 : ((Zlength (hk_2)) = nh)) (PreH31 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (IntArray.seg va_key_pre nv k_pre (replace_Znth ((nv - nv )) ((Znth p person_x 0)) (vk_tail_2)) )
  **  (IntArray.seg va_grp_pre nv k_pre (replace_Znth ((nv - nv )) (retval) (vg_tail_2)) )
  **  (IntArray.full va_grp_pre nv vg_2 )
  **  (IntArray.full va_key_pre nv vk_2 )
|--
  EX (vg: (@list Z))  (vk: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (0 <= (nv + 1 )) ” 
  &&  “ ((nv + 1 ) <= (p + 1 )) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= (p + 1 )) ” 
  &&  “ ((Zlength ((app (vg) ((cons (retval) ((@nil Z))))))) = (nv + 1 )) ” 
  &&  “ ((Zlength ((app (vk) ((cons ((Znth p person_x 0)) ((@nil Z))))))) = (nv + 1 )) ” 
  &&  “ ((Zlength (hg_2)) = nh) ” 
  &&  “ ((Zlength (hk_2)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - (nv + 1 ) )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - (nv + 1 ) )) ” 
  &&  “ ((Zlength (hg_tail_2)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail_2)) = (k_pre - nh )) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg_2 hk_2 ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg_2 hk_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) (app (vg) ((cons (retval) ((@nil Z))))) (app (vk) ((cons ((Znth p person_x 0)) ((@nil Z))))) hg_2 hk_2 ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) (app (vg) ((cons (retval) ((@nil Z))))) (app (vk) ((cons ((Znth p person_x 0)) ((@nil Z))))) hg_2 hk_2 ) ”
  &&  (IntArray.full va_grp_pre (nv + 1 ) (app (vg) ((cons (retval) ((@nil Z))))) )
  **  (IntArray.seg va_grp_pre (nv + 1 ) k_pre vg_tail )
  **  (IntArray.full va_key_pre (nv + 1 ) (app (vk) ((cons ((Znth p person_x 0)) ((@nil Z))))) )
  **  (IntArray.seg va_key_pre (nv + 1 ) k_pre vk_tail )
).

Definition solver_entail_wit_2_2 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 >= 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg_2)) = nv)) (PreH29 : ((Zlength (vk_2)) = nv)) (PreH30 : ((Zlength (hg_2)) = nh)) (PreH31 : ((Zlength (hk_2)) = nh)) (PreH32 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (IntArray.seg ha_key_pre nh k_pre (replace_Znth ((nh - nh )) ((Znth p person_y 0)) (hk_tail_2)) )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg ha_grp_pre nh k_pre (replace_Znth ((nh - nh )) (retval_2) (hg_tail_2)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full va_grp_pre nv vg_2 )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail_2 )
  **  (IntArray.full va_key_pre nv vk_2 )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail_2 )
  **  (IntArray.full ha_grp_pre nh hg_2 )
  **  (IntArray.full ha_key_pre nh hk_2 )
|--
  EX (vg: (@list Z))  (vk: (@list Z))  (hg: (@list Z))  (hk: (@list Z))  (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk_next: (@list Z))  (hg_next: (@list Z))  (vk_next: (@list Z))  (vg_next: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= (p + 1 )) ” 
  &&  “ (0 <= (nh + 1 )) ” 
  &&  “ ((nh + 1 ) <= (p + 1 )) ” 
  &&  “ ((Zlength (vg_next)) = nv) ” 
  &&  “ ((Zlength (vk_next)) = nv) ” 
  &&  “ ((Zlength (hg_next)) = (nh + 1 )) ” 
  &&  “ ((Zlength (hk_next)) = (nh + 1 )) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - (nh + 1 ) )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - (nh + 1 ) )) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (retval < 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (vg_next = vg) ” 
  &&  “ (vk_next = vk) ” 
  &&  “ (hg_next = (app (hg) ((cons (retval_2) ((@nil Z)))))) ” 
  &&  “ (hk_next = (app (hk) ((cons ((Znth p person_y 0)) ((@nil Z)))))) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre (nh + 1 ) hg_next )
  **  (IntArray.seg ha_grp_pre (nh + 1 ) k_pre hg_tail )
  **  (IntArray.full ha_key_pre (nh + 1 ) hk_next )
  **  (IntArray.seg ha_key_pre (nh + 1 ) k_pre hk_tail )
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 >= 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg_2)) = nv)) (PreH29 : ((Zlength (vk_2)) = nv)) (PreH30 : ((Zlength (hg_2)) = nh)) (PreH31 : ((Zlength (hk_2)) = nh)) (PreH32 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (IntArray.seg ha_key_pre nh k_pre (replace_Znth ((nh - nh )) ((Znth p person_y 0)) (hk_tail_2)) )
  **  (IntArray.seg ha_grp_pre nh k_pre (replace_Znth ((nh - nh )) (retval_2) (hg_tail_2)) )
  **  (IntArray.full ha_grp_pre nh hg_2 )
  **  (IntArray.full ha_key_pre nh hk_2 )
|--
  EX (hg: (@list Z))  (hk: (@list Z))  (hk_tail: (@list Z))  (hg_tail: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= (p + 1 )) ” 
  &&  “ (0 <= (nh + 1 )) ” 
  &&  “ ((nh + 1 ) <= (p + 1 )) ” 
  &&  “ ((Zlength (vg_2)) = nv) ” 
  &&  “ ((Zlength (vk_2)) = nv) ” 
  &&  “ ((Zlength ((app (hg) ((cons (retval_2) ((@nil Z))))))) = (nh + 1 )) ” 
  &&  “ ((Zlength ((app (hk) ((cons ((Znth p person_y 0)) ((@nil Z))))))) = (nh + 1 )) ” 
  &&  “ ((Zlength (vg_tail_2)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail_2)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - (nh + 1 ) )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - (nh + 1 ) )) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg hk ) ” 
  &&  “ (retval < 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_2 vk_2 (app (hg) ((cons (retval_2) ((@nil Z))))) (app (hk) ((cons ((Znth p person_y 0)) ((@nil Z))))) ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_2 vk_2 (app (hg) ((cons (retval_2) ((@nil Z))))) (app (hk) ((cons ((Znth p person_y 0)) ((@nil Z))))) ) ”
  &&  (IntArray.full ha_grp_pre (nh + 1 ) (app (hg) ((cons (retval_2) ((@nil Z))))) )
  **  (IntArray.seg ha_grp_pre (nh + 1 ) k_pre hg_tail )
  **  (IntArray.full ha_key_pre (nh + 1 ) (app (hk) ((cons ((Znth p person_y 0)) ((@nil Z))))) )
  **  (IntArray.seg ha_key_pre (nh + 1 ) k_pre hk_tail )
).

Definition solver_entail_wit_2_3 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 < 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg_2)) = nv)) (PreH29 : ((Zlength (vk_2)) = nv)) (PreH30 : ((Zlength (hg_2)) = nh)) (PreH31 : ((Zlength (hk_2)) = nh)) (PreH32 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_2 )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail_2 )
  **  (IntArray.full va_key_pre nv vk_2 )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail_2 )
  **  (IntArray.full ha_grp_pre nh hg_2 )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail_2 )
  **  (IntArray.full ha_key_pre nh hk_2 )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail_2 )
|--
  EX (vg: (@list Z))  (vk: (@list Z))  (hg: (@list Z))  (hk: (@list Z))  (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk_next: (@list Z))  (hg_next: (@list Z))  (vk_next: (@list Z))  (vg_next: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= (p + 1 )) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= (p + 1 )) ” 
  &&  “ ((Zlength (vg_next)) = nv) ” 
  &&  “ ((Zlength (vk_next)) = nv) ” 
  &&  “ ((Zlength (hg_next)) = nh) ” 
  &&  “ ((Zlength (hk_next)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (retval < 0) ” 
  &&  “ (retval_2 < 0) ” 
  &&  “ (vg_next = vg) ” 
  &&  “ (vk_next = vk) ” 
  &&  “ (hg_next = hg) ” 
  &&  “ (hk_next = hk) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 < 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg_2)) = nv)) (PreH29 : ((Zlength (vk_2)) = nv)) (PreH30 : ((Zlength (hg_2)) = nh)) (PreH31 : ((Zlength (hk_2)) = nh)) (PreH32 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  TT && emp 
|--
  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_2 vk_2 hg_2 hk_2 ) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_2 vk_2 hg_2 hk_2 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_2_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 < 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg_2)) = nv)) (PreH29 : ((Zlength (vk_2)) = nv)) (PreH30 : ((Zlength (hg_2)) = nh)) (PreH31 : ((Zlength (hk_2)) = nh)) (PreH32 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_2 vk_2 hg_2 hk_2 )
.

Definition solver_entail_wit_2_3_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 < 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg_2)) = nv)) (PreH29 : ((Zlength (vk_2)) = nv)) (PreH30 : ((Zlength (hg_2)) = nh)) (PreH31 : ((Zlength (hk_2)) = nh)) (PreH32 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_2 vk_2 hg_2 hk_2 )
.

Definition solver_entail_wit_2_3_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 < 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg_2)) = nv)) (PreH29 : ((Zlength (vk_2)) = nv)) (PreH30 : ((Zlength (hg_2)) = nh)) (PreH31 : ((Zlength (hk_2)) = nh)) (PreH32 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_3_1 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (0 <= sy)) (PreH36 : (vg_next = (app (vg_2) ((cons (sy) ((@nil Z))))))) (PreH37 : (vk_next = (app (vk_2) ((cons ((Znth p person_x 0)) ((@nil Z))))))) (PreH38 : (hg_next = hg_2)) (PreH39 : (hk_next = hk_2)) (PreH40 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH41 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail_2 )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail_2 )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail_2 )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail_2 )
|--
  EX (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk: (@list Z))  (hg: (@list Z))  (vk: (@list Z))  (vg: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= (p + 1 )) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= (p + 1 )) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg vk hg hk ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (0 <= sy)) (PreH36 : (vg_next = (app (vg_2) ((cons (sy) ((@nil Z))))))) (PreH37 : (vk_next = (app (vk_2) ((cons ((Znth p person_x 0)) ((@nil Z))))))) (PreH38 : (hg_next = hg_2)) (PreH39 : (hk_next = hk_2)) (PreH40 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH41 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (0 <= sy)) (PreH36 : (vg_next = (app (vg_2) ((cons (sy) ((@nil Z))))))) (PreH37 : (vk_next = (app (vk_2) ((cons ((Znth p person_x 0)) ((@nil Z))))))) (PreH38 : (hg_next = hg_2)) (PreH39 : (hk_next = hk_2)) (PreH40 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH41 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_3_2 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (sy < 0)) (PreH36 : (0 <= sx)) (PreH37 : (vg_next = vg_2)) (PreH38 : (vk_next = vk_2)) (PreH39 : (hg_next = (app (hg_2) ((cons (sx) ((@nil Z))))))) (PreH40 : (hk_next = (app (hk_2) ((cons ((Znth p person_y 0)) ((@nil Z))))))) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail_2 )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail_2 )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail_2 )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail_2 )
|--
  EX (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk: (@list Z))  (hg: (@list Z))  (vk: (@list Z))  (vg: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= (p + 1 )) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= (p + 1 )) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg vk hg hk ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (sy < 0)) (PreH36 : (0 <= sx)) (PreH37 : (vg_next = vg_2)) (PreH38 : (vk_next = vk_2)) (PreH39 : (hg_next = (app (hg_2) ((cons (sx) ((@nil Z))))))) (PreH40 : (hk_next = (app (hk_2) ((cons ((Znth p person_y 0)) ((@nil Z))))))) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (sy < 0)) (PreH36 : (0 <= sx)) (PreH37 : (vg_next = vg_2)) (PreH38 : (vk_next = vk_2)) (PreH39 : (hg_next = (app (hg_2) ((cons (sx) ((@nil Z))))))) (PreH40 : (hk_next = (app (hk_2) ((cons ((Znth p person_y 0)) ((@nil Z))))))) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_3_3 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (sy < 0)) (PreH36 : (sx < 0)) (PreH37 : (vg_next = vg_2)) (PreH38 : (vk_next = vk_2)) (PreH39 : (hg_next = hg_2)) (PreH40 : (hk_next = hk_2)) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_next )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail_2 )
  **  (IntArray.full va_key_pre nv vk_next )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail_2 )
  **  (IntArray.full ha_grp_pre nh hg_next )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail_2 )
  **  (IntArray.full ha_key_pre nh hk_next )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail_2 )
|--
  EX (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk: (@list Z))  (hg: (@list Z))  (vk: (@list Z))  (vg: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= (p + 1 )) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= (p + 1 )) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg vk hg hk ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (sy < 0)) (PreH36 : (sx < 0)) (PreH37 : (vg_next = vg_2)) (PreH38 : (vk_next = vk_2)) (PreH39 : (hg_next = hg_2)) (PreH40 : (hk_next = hk_2)) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  TT && emp 
|--
  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_3_3_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg_2: (@list Z)) (vk_2: (@list Z)) (hg_2: (@list Z)) (hk_2: (@list Z)) (vg_next: (@list Z)) (vk_next: (@list Z)) (hg_next: (@list Z)) (hk_next: (@list Z)) (vg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (hk_tail_2: (@list Z)) (p: Z) (nv: Z) (nh: Z) (sy: Z) (sx: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH17 : (0 <= p)) (PreH18 : (p < k_pre)) (PreH19 : (0 <= nv)) (PreH20 : (nv <= (p + 1 ))) (PreH21 : (0 <= nh)) (PreH22 : (nh <= (p + 1 ))) (PreH23 : ((Zlength (vg_next)) = nv)) (PreH24 : ((Zlength (vk_next)) = nv)) (PreH25 : ((Zlength (hg_next)) = nh)) (PreH26 : ((Zlength (hk_next)) = nh)) (PreH27 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH28 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH30 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH31 : (StripIndex y_lines (Znth p person_y 0) sy )) (PreH32 : (StripIndex x_lines (Znth p person_x 0) sx )) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH35 : (sy < 0)) (PreH36 : (sx < 0)) (PreH37 : (vg_next = vg_2)) (PreH38 : (vk_next = vk_2)) (PreH39 : (hg_next = hg_2)) (PreH40 : (hk_next = hk_2)) (PreH41 : (ClassifiedPrefix x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) (PreH42 : (ClassifiedCountsCorrect x_lines y_lines people (p + 1 ) vg_next vk_next hg_next hk_next )) ,
  forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))
.

Definition solver_entail_wit_4 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p >= k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg_2)) = nv)) (PreH25 : ((Zlength (vk_2)) = nv)) (PreH26 : ((Zlength (hg_2)) = nh)) (PreH27 : ((Zlength (hk_2)) = nh)) (PreH28 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg_2 )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail_2 )
  **  (IntArray.full va_key_pre nv vk_2 )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail_2 )
  **  (IntArray.full ha_grp_pre nh hg_2 )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail_2 )
  **  (IntArray.full ha_key_pre nh hk_2 )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail_2 )
|--
  EX (hk_tail: (@list Z))  (hg_tail: (@list Z))  (vk_tail: (@list Z))  (vg_tail: (@list Z))  (hk: (@list Z))  (hg: (@list Z))  (vk: (@list Z))  (vg: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p >= k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg_2)) = nv)) (PreH25 : ((Zlength (vk_2)) = nv)) (PreH26 : ((Zlength (hg_2)) = nh)) (PreH27 : ((Zlength (hk_2)) = nh)) (PreH28 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  TT && emp 
|--
  “ (ClassifiedCountsCorrect x_lines y_lines people k_pre vg_2 vk_2 hg_2 hk_2 ) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people k_pre vg_2 vk_2 hg_2 hk_2 ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p >= k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg_2)) = nv)) (PreH25 : ((Zlength (vk_2)) = nv)) (PreH26 : ((Zlength (hg_2)) = nh)) (PreH27 : ((Zlength (hk_2)) = nh)) (PreH28 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (ClassifiedCountsCorrect x_lines y_lines people k_pre vg_2 vk_2 hg_2 hk_2 )
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p >= k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg_2)) = nv)) (PreH25 : ((Zlength (vk_2)) = nv)) (PreH26 : ((Zlength (hg_2)) = nh)) (PreH27 : ((Zlength (hk_2)) = nh)) (PreH28 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  (ClassifiedPrefix x_lines y_lines people k_pre vg_2 vk_2 hg_2 hk_2 )
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail_2: (@list Z)) (hg_tail_2: (@list Z)) (vk_tail_2: (@list Z)) (vg_tail_2: (@list Z)) (hk_2: (@list Z)) (hg_2: (@list Z)) (vk_2: (@list Z)) (vg_2: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p >= k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q_2: Z) , (((0 <= q_2) /\ (q_2 < k_pre)) -> (((Znth q_2 person_x 0) = (fst ((Znth q_2 people __default__Prod_Z_Z)))) /\ ((Znth q_2 person_y 0) = (snd ((Znth q_2 people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg_2)) = nv)) (PreH25 : ((Zlength (vk_2)) = nv)) (PreH26 : ((Zlength (hg_2)) = nh)) (PreH27 : ((Zlength (hk_2)) = nh)) (PreH28 : ((Zlength (vg_tail_2)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail_2)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail_2)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail_2)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg_2 vk_2 hg_2 hk_2 )) ,
  forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))
.

Definition solver_return_wit_1 := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (Spec x_lines y_lines people (retval + retval_2 ) ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (Spec x_lines y_lines people (retval + retval_2 ) ) ”
  &&  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
).

Definition solver_return_wit_1_split_goal_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (Spec x_lines y_lines people (retval + retval_2 ) ) ”
.

Definition solver_return_wit_1_split_goal_spatial := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z) (keys_after_2: (@list Z)) (groups_after_2: (@list Z)) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after_2)) = nh)) (PreH2 : ((Zlength (keys_after_2)) = nh)) (PreH3 : (ParallelPermutation hg hk groups_after_2 keys_after_2 )) (PreH4 : (PairCountPrefix hg hk nh retval_2 )) (PreH5 : ((Zlength (groups_after)) = nv)) (PreH6 : ((Zlength (keys_after)) = nv)) (PreH7 : (ParallelPermutation vg vk groups_after keys_after )) (PreH8 : (PairCountPrefix vg vk nv retval )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 200000)) (PreH13 : (2 <= k_pre)) (PreH14 : (k_pre <= 300000)) (PreH15 : (n_pre = (Zlength (x_lines)))) (PreH16 : (m_pre = (Zlength (y_lines)))) (PreH17 : (k_pre = (Zlength (people)))) (PreH18 : ((Zlength (person_x)) = k_pre)) (PreH19 : ((Zlength (person_y)) = k_pre)) (PreH20 : (Pre x_lines y_lines people )) (PreH21 : (StreetCoordinateBounds x_lines )) (PreH22 : (StreetCoordinateBounds y_lines )) (PreH23 : (PeopleCoordinateBounds people )) (PreH24 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full ha_grp_pre nh groups_after_2 )
  **  (IntArray.full ha_key_pre nh keys_after_2 )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  (IntArray.full_shape va_grp_pre k_pre )
  **  (IntArray.full_shape va_key_pre k_pre )
  **  (IntArray.full_shape ha_grp_pre k_pre )
  **  (IntArray.full_shape ha_key_pre k_pre )
.

Definition solver_partial_solve_wit_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p < k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg)) = nv)) (PreH25 : ((Zlength (vk)) = nv)) (PreH26 : ((Zlength (hg)) = nh)) (PreH27 : ((Zlength (hk)) = nh)) (PreH28 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((py_pre + (p * sizeof(INT)))) # Int  |-> (Znth p person_y 0))
  **  (IntArray.missing_i py_pre p 0 k_pre person_y )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_2_pure := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p < k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg)) = nv)) (PreH25 : ((Zlength (vk)) = nv)) (PreH26 : ((Zlength (hg)) = nh)) (PreH27 : ((Zlength (hk)) = nh)) (PreH28 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ ((Zlength (y_lines)) = m_pre) ” 
  &&  “ ((Znth p person_y 0) <= 1000000) ” 
  &&  “ (0 <= (Znth p person_y 0)) ” 
  &&  “ ((Znth (m_pre - 1 ) y_lines 0) = 1000000) ” 
  &&  “ ((Znth 0 y_lines 0) = 0) ” 
  &&  “ (mono_inc y_lines ) ”
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (nh >= INT_MIN)) (PreH8 : (nv >= INT_MIN)) (PreH9 : (p >= INT_MIN)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (p < k_pre)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= m_pre)) (PreH17 : (m_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= 300000)) (PreH20 : (n_pre = (Zlength (x_lines)))) (PreH21 : (m_pre = (Zlength (y_lines)))) (PreH22 : (k_pre = (Zlength (people)))) (PreH23 : ((Zlength (person_x)) = k_pre)) (PreH24 : ((Zlength (person_y)) = k_pre)) (PreH25 : (Pre x_lines y_lines people )) (PreH26 : (StreetCoordinateBounds x_lines )) (PreH27 : (StreetCoordinateBounds y_lines )) (PreH28 : (PeopleCoordinateBounds people )) (PreH29 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH30 : (0 <= p)) (PreH31 : (p <= k_pre)) (PreH32 : (0 <= nv)) (PreH33 : (nv <= p)) (PreH34 : (0 <= nh)) (PreH35 : (nh <= p)) (PreH36 : ((Zlength (vg)) = nv)) (PreH37 : ((Zlength (vk)) = nv)) (PreH38 : ((Zlength (hg)) = nh)) (PreH39 : ((Zlength (hk)) = nh)) (PreH40 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH41 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH42 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH43 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH44 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH45 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (mono_inc y_lines ) ” 
  &&  “ ((Znth 0 y_lines 0) = 0) ” 
  &&  “ ((Znth (m_pre - 1 ) y_lines 0) = 1000000) ” 
  &&  “ (0 <= (Znth p person_y 0)) ” 
  &&  “ ((Znth p person_y 0) <= 1000000) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (nh >= INT_MIN)) (PreH8 : (nv >= INT_MIN)) (PreH9 : (p >= INT_MIN)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (p < k_pre)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= m_pre)) (PreH17 : (m_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= 300000)) (PreH20 : (n_pre = (Zlength (x_lines)))) (PreH21 : (m_pre = (Zlength (y_lines)))) (PreH22 : (k_pre = (Zlength (people)))) (PreH23 : ((Zlength (person_x)) = k_pre)) (PreH24 : ((Zlength (person_y)) = k_pre)) (PreH25 : (Pre x_lines y_lines people )) (PreH26 : (StreetCoordinateBounds x_lines )) (PreH27 : (StreetCoordinateBounds y_lines )) (PreH28 : (PeopleCoordinateBounds people )) (PreH29 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH30 : (0 <= p)) (PreH31 : (p <= k_pre)) (PreH32 : (0 <= nv)) (PreH33 : (nv <= p)) (PreH34 : (0 <= nh)) (PreH35 : (nh <= p)) (PreH36 : ((Zlength (vg)) = nv)) (PreH37 : ((Zlength (vk)) = nv)) (PreH38 : ((Zlength (hg)) = nh)) (PreH39 : ((Zlength (hk)) = nh)) (PreH40 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH41 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH42 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH43 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH44 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH45 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (mono_inc y_lines ) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_2 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (nh >= INT_MIN)) (PreH8 : (nv >= INT_MIN)) (PreH9 : (p >= INT_MIN)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (p < k_pre)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= m_pre)) (PreH17 : (m_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= 300000)) (PreH20 : (n_pre = (Zlength (x_lines)))) (PreH21 : (m_pre = (Zlength (y_lines)))) (PreH22 : (k_pre = (Zlength (people)))) (PreH23 : ((Zlength (person_x)) = k_pre)) (PreH24 : ((Zlength (person_y)) = k_pre)) (PreH25 : (Pre x_lines y_lines people )) (PreH26 : (StreetCoordinateBounds x_lines )) (PreH27 : (StreetCoordinateBounds y_lines )) (PreH28 : (PeopleCoordinateBounds people )) (PreH29 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH30 : (0 <= p)) (PreH31 : (p <= k_pre)) (PreH32 : (0 <= nv)) (PreH33 : (nv <= p)) (PreH34 : (0 <= nh)) (PreH35 : (nh <= p)) (PreH36 : ((Zlength (vg)) = nv)) (PreH37 : ((Zlength (vk)) = nv)) (PreH38 : ((Zlength (hg)) = nh)) (PreH39 : ((Zlength (hk)) = nh)) (PreH40 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH41 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH42 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH43 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH44 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH45 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((Znth 0 y_lines 0) = 0) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_3 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (nh >= INT_MIN)) (PreH8 : (nv >= INT_MIN)) (PreH9 : (p >= INT_MIN)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (p < k_pre)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= m_pre)) (PreH17 : (m_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= 300000)) (PreH20 : (n_pre = (Zlength (x_lines)))) (PreH21 : (m_pre = (Zlength (y_lines)))) (PreH22 : (k_pre = (Zlength (people)))) (PreH23 : ((Zlength (person_x)) = k_pre)) (PreH24 : ((Zlength (person_y)) = k_pre)) (PreH25 : (Pre x_lines y_lines people )) (PreH26 : (StreetCoordinateBounds x_lines )) (PreH27 : (StreetCoordinateBounds y_lines )) (PreH28 : (PeopleCoordinateBounds people )) (PreH29 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH30 : (0 <= p)) (PreH31 : (p <= k_pre)) (PreH32 : (0 <= nv)) (PreH33 : (nv <= p)) (PreH34 : (0 <= nh)) (PreH35 : (nh <= p)) (PreH36 : ((Zlength (vg)) = nv)) (PreH37 : ((Zlength (vk)) = nv)) (PreH38 : ((Zlength (hg)) = nh)) (PreH39 : ((Zlength (hk)) = nh)) (PreH40 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH41 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH42 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH43 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH44 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH45 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((Znth (m_pre - 1 ) y_lines 0) = 1000000) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_4 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (nh >= INT_MIN)) (PreH8 : (nv >= INT_MIN)) (PreH9 : (p >= INT_MIN)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (p < k_pre)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= m_pre)) (PreH17 : (m_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= 300000)) (PreH20 : (n_pre = (Zlength (x_lines)))) (PreH21 : (m_pre = (Zlength (y_lines)))) (PreH22 : (k_pre = (Zlength (people)))) (PreH23 : ((Zlength (person_x)) = k_pre)) (PreH24 : ((Zlength (person_y)) = k_pre)) (PreH25 : (Pre x_lines y_lines people )) (PreH26 : (StreetCoordinateBounds x_lines )) (PreH27 : (StreetCoordinateBounds y_lines )) (PreH28 : (PeopleCoordinateBounds people )) (PreH29 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH30 : (0 <= p)) (PreH31 : (p <= k_pre)) (PreH32 : (0 <= nv)) (PreH33 : (nv <= p)) (PreH34 : (0 <= nh)) (PreH35 : (nh <= p)) (PreH36 : ((Zlength (vg)) = nv)) (PreH37 : ((Zlength (vk)) = nv)) (PreH38 : ((Zlength (hg)) = nh)) (PreH39 : ((Zlength (hk)) = nh)) (PreH40 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH41 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH42 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH43 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH44 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH45 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= (Znth p person_y 0)) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_5 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (nh >= INT_MIN)) (PreH8 : (nv >= INT_MIN)) (PreH9 : (p >= INT_MIN)) (PreH10 : (k_pre >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (p < k_pre)) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (2 <= m_pre)) (PreH17 : (m_pre <= 200000)) (PreH18 : (2 <= k_pre)) (PreH19 : (k_pre <= 300000)) (PreH20 : (n_pre = (Zlength (x_lines)))) (PreH21 : (m_pre = (Zlength (y_lines)))) (PreH22 : (k_pre = (Zlength (people)))) (PreH23 : ((Zlength (person_x)) = k_pre)) (PreH24 : ((Zlength (person_y)) = k_pre)) (PreH25 : (Pre x_lines y_lines people )) (PreH26 : (StreetCoordinateBounds x_lines )) (PreH27 : (StreetCoordinateBounds y_lines )) (PreH28 : (PeopleCoordinateBounds people )) (PreH29 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH30 : (0 <= p)) (PreH31 : (p <= k_pre)) (PreH32 : (0 <= nv)) (PreH33 : (nv <= p)) (PreH34 : (0 <= nh)) (PreH35 : (nh <= p)) (PreH36 : ((Zlength (vg)) = nv)) (PreH37 : ((Zlength (vk)) = nv)) (PreH38 : ((Zlength (hg)) = nh)) (PreH39 : ((Zlength (hk)) = nh)) (PreH40 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH41 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH42 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH43 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH44 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH45 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |->_)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((Znth p person_y 0) <= 1000000) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z)  __default__Prod_Z_Z (PreH1 : (p < k_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (2 <= m_pre)) (PreH5 : (m_pre <= 200000)) (PreH6 : (2 <= k_pre)) (PreH7 : (k_pre <= 300000)) (PreH8 : (n_pre = (Zlength (x_lines)))) (PreH9 : (m_pre = (Zlength (y_lines)))) (PreH10 : (k_pre = (Zlength (people)))) (PreH11 : ((Zlength (person_x)) = k_pre)) (PreH12 : ((Zlength (person_y)) = k_pre)) (PreH13 : (Pre x_lines y_lines people )) (PreH14 : (StreetCoordinateBounds x_lines )) (PreH15 : (StreetCoordinateBounds y_lines )) (PreH16 : (PeopleCoordinateBounds people )) (PreH17 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH18 : (0 <= p)) (PreH19 : (p <= k_pre)) (PreH20 : (0 <= nv)) (PreH21 : (nv <= p)) (PreH22 : (0 <= nh)) (PreH23 : (nh <= p)) (PreH24 : ((Zlength (vg)) = nv)) (PreH25 : ((Zlength (vk)) = nv)) (PreH26 : ((Zlength (hg)) = nh)) (PreH27 : ((Zlength (hk)) = nh)) (PreH28 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH29 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH31 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH32 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH33 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ ((Zlength (y_lines)) = m_pre) ” 
  &&  “ ((Znth p person_y 0) <= 1000000) ” 
  &&  “ (0 <= (Znth p person_y 0)) ” 
  &&  “ ((Znth (m_pre - 1 ) y_lines 0) = 1000000) ” 
  &&  “ ((Znth 0 y_lines 0) = 0) ” 
  &&  “ (mono_inc y_lines ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH2 : (p < k_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : (2 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (x_lines)))) (PreH10 : (m_pre = (Zlength (y_lines)))) (PreH11 : (k_pre = (Zlength (people)))) (PreH12 : ((Zlength (person_x)) = k_pre)) (PreH13 : ((Zlength (person_y)) = k_pre)) (PreH14 : (Pre x_lines y_lines people )) (PreH15 : (StreetCoordinateBounds x_lines )) (PreH16 : (StreetCoordinateBounds y_lines )) (PreH17 : (PeopleCoordinateBounds people )) (PreH18 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH19 : (0 <= p)) (PreH20 : (p <= k_pre)) (PreH21 : (0 <= nv)) (PreH22 : (nv <= p)) (PreH23 : (0 <= nh)) (PreH24 : (nh <= p)) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((px_pre + (p * sizeof(INT)))) # Int  |-> (Znth p person_x 0))
  **  (IntArray.missing_i px_pre p 0 k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_4_pure := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH2 : (p < k_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : (2 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (x_lines)))) (PreH10 : (m_pre = (Zlength (y_lines)))) (PreH11 : (k_pre = (Zlength (people)))) (PreH12 : ((Zlength (person_x)) = k_pre)) (PreH13 : ((Zlength (person_y)) = k_pre)) (PreH14 : (Pre x_lines y_lines people )) (PreH15 : (StreetCoordinateBounds x_lines )) (PreH16 : (StreetCoordinateBounds y_lines )) (PreH17 : (PeopleCoordinateBounds people )) (PreH18 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH19 : (0 <= p)) (PreH20 : (p <= k_pre)) (PreH21 : (0 <= nv)) (PreH22 : (nv <= p)) (PreH23 : (0 <= nh)) (PreH24 : (nh <= p)) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |->_)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (x_lines)) = n_pre) ” 
  &&  “ ((Znth p person_x 0) <= 1000000) ” 
  &&  “ (0 <= (Znth p person_x 0)) ” 
  &&  “ ((Znth (n_pre - 1 ) x_lines 0) = 1000000) ” 
  &&  “ ((Znth 0 x_lines 0) = 0) ” 
  &&  “ (mono_inc x_lines ) ”
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (nh >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH16 : (p < k_pre)) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= m_pre)) (PreH20 : (m_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= 300000)) (PreH23 : (n_pre = (Zlength (x_lines)))) (PreH24 : (m_pre = (Zlength (y_lines)))) (PreH25 : (k_pre = (Zlength (people)))) (PreH26 : ((Zlength (person_x)) = k_pre)) (PreH27 : ((Zlength (person_y)) = k_pre)) (PreH28 : (Pre x_lines y_lines people )) (PreH29 : (StreetCoordinateBounds x_lines )) (PreH30 : (StreetCoordinateBounds y_lines )) (PreH31 : (PeopleCoordinateBounds people )) (PreH32 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH33 : (0 <= p)) (PreH34 : (p <= k_pre)) (PreH35 : (0 <= nv)) (PreH36 : (nv <= p)) (PreH37 : (0 <= nh)) (PreH38 : (nh <= p)) (PreH39 : ((Zlength (vg)) = nv)) (PreH40 : ((Zlength (vk)) = nv)) (PreH41 : ((Zlength (hg)) = nh)) (PreH42 : ((Zlength (hk)) = nh)) (PreH43 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH44 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH45 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH46 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH47 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH48 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |->_)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (mono_inc x_lines ) ” 
  &&  “ ((Znth 0 x_lines 0) = 0) ” 
  &&  “ ((Znth (n_pre - 1 ) x_lines 0) = 1000000) ” 
  &&  “ (0 <= (Znth p person_x 0)) ” 
  &&  “ ((Znth p person_x 0) <= 1000000) ”
).

Definition solver_partial_solve_wit_4_pure_split_goal_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (nh >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH16 : (p < k_pre)) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= m_pre)) (PreH20 : (m_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= 300000)) (PreH23 : (n_pre = (Zlength (x_lines)))) (PreH24 : (m_pre = (Zlength (y_lines)))) (PreH25 : (k_pre = (Zlength (people)))) (PreH26 : ((Zlength (person_x)) = k_pre)) (PreH27 : ((Zlength (person_y)) = k_pre)) (PreH28 : (Pre x_lines y_lines people )) (PreH29 : (StreetCoordinateBounds x_lines )) (PreH30 : (StreetCoordinateBounds y_lines )) (PreH31 : (PeopleCoordinateBounds people )) (PreH32 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH33 : (0 <= p)) (PreH34 : (p <= k_pre)) (PreH35 : (0 <= nv)) (PreH36 : (nv <= p)) (PreH37 : (0 <= nh)) (PreH38 : (nh <= p)) (PreH39 : ((Zlength (vg)) = nv)) (PreH40 : ((Zlength (vk)) = nv)) (PreH41 : ((Zlength (hg)) = nh)) (PreH42 : ((Zlength (hk)) = nh)) (PreH43 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH44 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH45 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH46 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH47 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH48 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |->_)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (mono_inc x_lines ) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_2 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (nh >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH16 : (p < k_pre)) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= m_pre)) (PreH20 : (m_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= 300000)) (PreH23 : (n_pre = (Zlength (x_lines)))) (PreH24 : (m_pre = (Zlength (y_lines)))) (PreH25 : (k_pre = (Zlength (people)))) (PreH26 : ((Zlength (person_x)) = k_pre)) (PreH27 : ((Zlength (person_y)) = k_pre)) (PreH28 : (Pre x_lines y_lines people )) (PreH29 : (StreetCoordinateBounds x_lines )) (PreH30 : (StreetCoordinateBounds y_lines )) (PreH31 : (PeopleCoordinateBounds people )) (PreH32 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH33 : (0 <= p)) (PreH34 : (p <= k_pre)) (PreH35 : (0 <= nv)) (PreH36 : (nv <= p)) (PreH37 : (0 <= nh)) (PreH38 : (nh <= p)) (PreH39 : ((Zlength (vg)) = nv)) (PreH40 : ((Zlength (vk)) = nv)) (PreH41 : ((Zlength (hg)) = nh)) (PreH42 : ((Zlength (hk)) = nh)) (PreH43 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH44 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH45 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH46 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH47 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH48 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |->_)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((Znth 0 x_lines 0) = 0) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_3 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (nh >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH16 : (p < k_pre)) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= m_pre)) (PreH20 : (m_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= 300000)) (PreH23 : (n_pre = (Zlength (x_lines)))) (PreH24 : (m_pre = (Zlength (y_lines)))) (PreH25 : (k_pre = (Zlength (people)))) (PreH26 : ((Zlength (person_x)) = k_pre)) (PreH27 : ((Zlength (person_y)) = k_pre)) (PreH28 : (Pre x_lines y_lines people )) (PreH29 : (StreetCoordinateBounds x_lines )) (PreH30 : (StreetCoordinateBounds y_lines )) (PreH31 : (PeopleCoordinateBounds people )) (PreH32 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH33 : (0 <= p)) (PreH34 : (p <= k_pre)) (PreH35 : (0 <= nv)) (PreH36 : (nv <= p)) (PreH37 : (0 <= nh)) (PreH38 : (nh <= p)) (PreH39 : ((Zlength (vg)) = nv)) (PreH40 : ((Zlength (vk)) = nv)) (PreH41 : ((Zlength (hg)) = nh)) (PreH42 : ((Zlength (hk)) = nh)) (PreH43 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH44 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH45 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH46 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH47 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH48 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |->_)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((Znth (n_pre - 1 ) x_lines 0) = 1000000) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_4 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (nh >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH16 : (p < k_pre)) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= m_pre)) (PreH20 : (m_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= 300000)) (PreH23 : (n_pre = (Zlength (x_lines)))) (PreH24 : (m_pre = (Zlength (y_lines)))) (PreH25 : (k_pre = (Zlength (people)))) (PreH26 : ((Zlength (person_x)) = k_pre)) (PreH27 : ((Zlength (person_y)) = k_pre)) (PreH28 : (Pre x_lines y_lines people )) (PreH29 : (StreetCoordinateBounds x_lines )) (PreH30 : (StreetCoordinateBounds y_lines )) (PreH31 : (PeopleCoordinateBounds people )) (PreH32 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH33 : (0 <= p)) (PreH34 : (p <= k_pre)) (PreH35 : (0 <= nv)) (PreH36 : (nv <= p)) (PreH37 : (0 <= nh)) (PreH38 : (nh <= p)) (PreH39 : ((Zlength (vg)) = nv)) (PreH40 : ((Zlength (vk)) = nv)) (PreH41 : ((Zlength (hg)) = nh)) (PreH42 : ((Zlength (hk)) = nh)) (PreH43 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH44 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH45 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH46 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH47 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH48 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |->_)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= (Znth p person_x 0)) ”
.

Definition solver_partial_solve_wit_4_pure_split_goal_5 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (p <= INT_MAX)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (nh >= INT_MIN)) (PreH9 : (nv >= INT_MIN)) (PreH10 : (p >= INT_MIN)) (PreH11 : (k_pre >= INT_MIN)) (PreH12 : (m_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (retval >= INT_MIN)) (PreH15 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH16 : (p < k_pre)) (PreH17 : (2 <= n_pre)) (PreH18 : (n_pre <= 200000)) (PreH19 : (2 <= m_pre)) (PreH20 : (m_pre <= 200000)) (PreH21 : (2 <= k_pre)) (PreH22 : (k_pre <= 300000)) (PreH23 : (n_pre = (Zlength (x_lines)))) (PreH24 : (m_pre = (Zlength (y_lines)))) (PreH25 : (k_pre = (Zlength (people)))) (PreH26 : ((Zlength (person_x)) = k_pre)) (PreH27 : ((Zlength (person_y)) = k_pre)) (PreH28 : (Pre x_lines y_lines people )) (PreH29 : (StreetCoordinateBounds x_lines )) (PreH30 : (StreetCoordinateBounds y_lines )) (PreH31 : (PeopleCoordinateBounds people )) (PreH32 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH33 : (0 <= p)) (PreH34 : (p <= k_pre)) (PreH35 : (0 <= nv)) (PreH36 : (nv <= p)) (PreH37 : (0 <= nh)) (PreH38 : (nh <= p)) (PreH39 : ((Zlength (vg)) = nv)) (PreH40 : ((Zlength (vk)) = nv)) (PreH41 : ((Zlength (hg)) = nh)) (PreH42 : ((Zlength (hk)) = nh)) (PreH43 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH44 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH45 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH46 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH47 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH48 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  ((( &( "sx" ) )) # Int  |->_)
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  ((( &( "sy" ) )) # Int  |-> retval)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ ((Znth p person_x 0) <= 1000000) ”
.

Definition solver_partial_solve_wit_4_aux := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z)  __default__Prod_Z_Z (PreH1 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH2 : (p < k_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (2 <= m_pre)) (PreH6 : (m_pre <= 200000)) (PreH7 : (2 <= k_pre)) (PreH8 : (k_pre <= 300000)) (PreH9 : (n_pre = (Zlength (x_lines)))) (PreH10 : (m_pre = (Zlength (y_lines)))) (PreH11 : (k_pre = (Zlength (people)))) (PreH12 : ((Zlength (person_x)) = k_pre)) (PreH13 : ((Zlength (person_y)) = k_pre)) (PreH14 : (Pre x_lines y_lines people )) (PreH15 : (StreetCoordinateBounds x_lines )) (PreH16 : (StreetCoordinateBounds y_lines )) (PreH17 : (PeopleCoordinateBounds people )) (PreH18 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH19 : (0 <= p)) (PreH20 : (p <= k_pre)) (PreH21 : (0 <= nv)) (PreH22 : (nv <= p)) (PreH23 : (0 <= nh)) (PreH24 : (nh <= p)) (PreH25 : ((Zlength (vg)) = nv)) (PreH26 : ((Zlength (vk)) = nv)) (PreH27 : ((Zlength (hg)) = nh)) (PreH28 : ((Zlength (hk)) = nh)) (PreH29 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH30 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH31 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH32 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH33 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH34 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (x_lines)) = n_pre) ” 
  &&  “ ((Znth p person_x 0) <= 1000000) ” 
  &&  “ (0 <= (Znth p person_x 0)) ” 
  &&  “ ((Znth (n_pre - 1 ) x_lines 0) = 1000000) ” 
  &&  “ ((Znth 0 x_lines 0) = 0) ” 
  &&  “ (mono_inc x_lines ) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval >= 0)) (PreH2 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH3 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH4 : (p < k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH21 : (0 <= p)) (PreH22 : (p <= k_pre)) (PreH23 : (0 <= nv)) (PreH24 : (nv <= p)) (PreH25 : (0 <= nh)) (PreH26 : (nh <= p)) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (retval >= 0) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((va_grp_pre + (nv * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i va_grp_pre nv nv k_pre vg_tail )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_6 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval >= 0)) (PreH2 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH3 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH4 : (p < k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH21 : (0 <= p)) (PreH22 : (p <= k_pre)) (PreH23 : (0 <= nv)) (PreH24 : (nv <= p)) (PreH25 : (0 <= nh)) (PreH26 : (nh <= p)) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.seg va_grp_pre nv k_pre (replace_Znth ((nv - nv )) (retval) (vg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (retval >= 0) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((px_pre + (p * sizeof(INT)))) # Int  |-> (Znth p person_x 0))
  **  (IntArray.missing_i px_pre p 0 k_pre person_x )
  **  (IntArray.seg va_grp_pre nv k_pre (replace_Znth ((nv - nv )) (retval) (vg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_7 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval >= 0)) (PreH2 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH3 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH4 : (p < k_pre)) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH21 : (0 <= p)) (PreH22 : (p <= k_pre)) (PreH23 : (0 <= nv)) (PreH24 : (nv <= p)) (PreH25 : (0 <= nh)) (PreH26 : (nh <= p)) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.seg va_grp_pre nv k_pre (replace_Znth ((nv - nv )) (retval) (vg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (retval >= 0) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((va_key_pre + (nv * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i va_key_pre nv nv k_pre vk_tail )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.seg va_grp_pre nv k_pre (replace_Znth ((nv - nv )) (retval) (vg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_8 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 >= 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg)) = nv)) (PreH29 : ((Zlength (vk)) = nv)) (PreH30 : ((Zlength (hg)) = nh)) (PreH31 : ((Zlength (hk)) = nh)) (PreH32 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (retval_2 >= 0) ” 
  &&  “ (retval < 0) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((ha_grp_pre + (nh * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ha_grp_pre nh nh k_pre hg_tail )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_9 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 >= 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg)) = nv)) (PreH29 : ((Zlength (vk)) = nv)) (PreH30 : ((Zlength (hg)) = nh)) (PreH31 : ((Zlength (hk)) = nh)) (PreH32 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.seg ha_grp_pre nh k_pre (replace_Znth ((nh - nh )) (retval_2) (hg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (retval_2 >= 0) ” 
  &&  “ (retval < 0) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((py_pre + (p * sizeof(INT)))) # Int  |-> (Znth p person_y 0))
  **  (IntArray.missing_i py_pre p 0 k_pre person_y )
  **  (IntArray.seg ha_grp_pre nh k_pre (replace_Znth ((nh - nh )) (retval_2) (hg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_10 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (hk_tail: (@list Z)) (hg_tail: (@list Z)) (vk_tail: (@list Z)) (vg_tail: (@list Z)) (hk: (@list Z)) (hg: (@list Z)) (vk: (@list Z)) (vg: (@list Z)) (nh: Z) (nv: Z) (p: Z) (retval: Z) (retval_2: Z)  __default__Prod_Z_Z (PreH1 : (retval_2 >= 0)) (PreH2 : (retval < 0)) (PreH3 : (StripIndex x_lines (Znth p person_x 0) retval_2 )) (PreH4 : (StripIndex y_lines (Znth p person_y 0) retval )) (PreH5 : (p < k_pre)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (2 <= m_pre)) (PreH9 : (m_pre <= 200000)) (PreH10 : (2 <= k_pre)) (PreH11 : (k_pre <= 300000)) (PreH12 : (n_pre = (Zlength (x_lines)))) (PreH13 : (m_pre = (Zlength (y_lines)))) (PreH14 : (k_pre = (Zlength (people)))) (PreH15 : ((Zlength (person_x)) = k_pre)) (PreH16 : ((Zlength (person_y)) = k_pre)) (PreH17 : (Pre x_lines y_lines people )) (PreH18 : (StreetCoordinateBounds x_lines )) (PreH19 : (StreetCoordinateBounds y_lines )) (PreH20 : (PeopleCoordinateBounds people )) (PreH21 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH22 : (0 <= p)) (PreH23 : (p <= k_pre)) (PreH24 : (0 <= nv)) (PreH25 : (nv <= p)) (PreH26 : (0 <= nh)) (PreH27 : (nh <= p)) (PreH28 : ((Zlength (vg)) = nv)) (PreH29 : ((Zlength (vk)) = nv)) (PreH30 : ((Zlength (hg)) = nh)) (PreH31 : ((Zlength (hk)) = nh)) (PreH32 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH34 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH35 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH36 : (ClassifiedPrefix x_lines y_lines people p vg vk hg hk )) (PreH37 : (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk )) ,
  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg ha_grp_pre nh k_pre (replace_Znth ((nh - nh )) (retval_2) (hg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (retval_2 >= 0) ” 
  &&  “ (retval < 0) ” 
  &&  “ (StripIndex x_lines (Znth p person_x 0) retval_2 ) ” 
  &&  “ (StripIndex y_lines (Znth p person_y 0) retval ) ” 
  &&  “ (p < k_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (nv <= p) ” 
  &&  “ (0 <= nh) ” 
  &&  “ (nh <= p) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people p vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people p vg vk hg hk ) ”
  &&  (((ha_key_pre + (nh * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ha_key_pre nh nh k_pre hk_tail )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg ha_grp_pre nh k_pre (replace_Znth ((nh - nh )) (retval_2) (hg_tail)) )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.full ha_key_pre nh hk )
.

Definition solver_partial_solve_wit_11_pure := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (vg)) = nv)) (PreH18 : ((Zlength (vk)) = nv)) (PreH19 : ((Zlength (hg)) = nh)) (PreH20 : ((Zlength (hk)) = nh)) (PreH21 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH22 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH23 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH24 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH25 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH26 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (k_pre <= 300000) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ (nv <= k_pre) ” 
  &&  “ (0 <= nv) ”
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (nh >= INT_MIN)) (PreH7 : (nv >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : (2 <= m_pre)) (PreH14 : (m_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= 300000)) (PreH17 : (n_pre = (Zlength (x_lines)))) (PreH18 : (m_pre = (Zlength (y_lines)))) (PreH19 : (k_pre = (Zlength (people)))) (PreH20 : ((Zlength (person_x)) = k_pre)) (PreH21 : ((Zlength (person_y)) = k_pre)) (PreH22 : (Pre x_lines y_lines people )) (PreH23 : (StreetCoordinateBounds x_lines )) (PreH24 : (StreetCoordinateBounds y_lines )) (PreH25 : (PeopleCoordinateBounds people )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= nv) ” 
  &&  “ (nv <= k_pre) ”
).

Definition solver_partial_solve_wit_11_pure_split_goal_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (nh >= INT_MIN)) (PreH7 : (nv >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : (2 <= m_pre)) (PreH14 : (m_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= 300000)) (PreH17 : (n_pre = (Zlength (x_lines)))) (PreH18 : (m_pre = (Zlength (y_lines)))) (PreH19 : (k_pre = (Zlength (people)))) (PreH20 : ((Zlength (person_x)) = k_pre)) (PreH21 : ((Zlength (person_y)) = k_pre)) (PreH22 : (Pre x_lines y_lines people )) (PreH23 : (StreetCoordinateBounds x_lines )) (PreH24 : (StreetCoordinateBounds y_lines )) (PreH25 : (PeopleCoordinateBounds people )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= nv) ”
.

Definition solver_partial_solve_wit_11_pure_split_goal_2 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (nh >= INT_MIN)) (PreH7 : (nv >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 200000)) (PreH13 : (2 <= m_pre)) (PreH14 : (m_pre <= 200000)) (PreH15 : (2 <= k_pre)) (PreH16 : (k_pre <= 300000)) (PreH17 : (n_pre = (Zlength (x_lines)))) (PreH18 : (m_pre = (Zlength (y_lines)))) (PreH19 : (k_pre = (Zlength (people)))) (PreH20 : ((Zlength (person_x)) = k_pre)) (PreH21 : ((Zlength (person_y)) = k_pre)) (PreH22 : (Pre x_lines y_lines people )) (PreH23 : (StreetCoordinateBounds x_lines )) (PreH24 : (StreetCoordinateBounds y_lines )) (PreH25 : (PeopleCoordinateBounds people )) (PreH26 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH27 : ((Zlength (vg)) = nv)) (PreH28 : ((Zlength (vk)) = nv)) (PreH29 : ((Zlength (hg)) = nh)) (PreH30 : ((Zlength (hk)) = nh)) (PreH31 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH32 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH33 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH34 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH35 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH36 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (nv <= k_pre) ”
.

Definition solver_partial_solve_wit_11_aux := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z)  __default__Prod_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 200000)) (PreH5 : (2 <= k_pre)) (PreH6 : (k_pre <= 300000)) (PreH7 : (n_pre = (Zlength (x_lines)))) (PreH8 : (m_pre = (Zlength (y_lines)))) (PreH9 : (k_pre = (Zlength (people)))) (PreH10 : ((Zlength (person_x)) = k_pre)) (PreH11 : ((Zlength (person_y)) = k_pre)) (PreH12 : (Pre x_lines y_lines people )) (PreH13 : (StreetCoordinateBounds x_lines )) (PreH14 : (StreetCoordinateBounds y_lines )) (PreH15 : (PeopleCoordinateBounds people )) (PreH16 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH17 : ((Zlength (vg)) = nv)) (PreH18 : ((Zlength (vk)) = nv)) (PreH19 : ((Zlength (hg)) = nh)) (PreH20 : ((Zlength (hk)) = nh)) (PreH21 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH22 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH23 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH24 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH25 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH26 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (k_pre <= 300000) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ (nv <= k_pre) ” 
  &&  “ (0 <= nv) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk ) ”
  &&  (IntArray.full va_grp_pre nv vg )
  **  (IntArray.full va_key_pre nv vk )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_11 := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux.

Definition solver_partial_solve_wit_12_pure := 
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after)) = nv)) (PreH2 : ((Zlength (keys_after)) = nv)) (PreH3 : (ParallelPermutation vg vk groups_after keys_after )) (PreH4 : (PairCountPrefix vg vk nv retval )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH21 : ((Zlength (vg)) = nv)) (PreH22 : ((Zlength (vk)) = nv)) (PreH23 : ((Zlength (hg)) = nh)) (PreH24 : ((Zlength (hk)) = nh)) (PreH25 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH26 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH27 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH28 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH29 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH30 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (k_pre <= 300000) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ (nh <= k_pre) ” 
  &&  “ (0 <= nh) ”
) \/
(
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (nh >= INT_MIN)) (PreH7 : (nv >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : ((Zlength (groups_after)) = nv)) (PreH12 : ((Zlength (keys_after)) = nv)) (PreH13 : (ParallelPermutation vg vk groups_after keys_after )) (PreH14 : (PairCountPrefix vg vk nv retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= m_pre)) (PreH18 : (m_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= 300000)) (PreH21 : (n_pre = (Zlength (x_lines)))) (PreH22 : (m_pre = (Zlength (y_lines)))) (PreH23 : (k_pre = (Zlength (people)))) (PreH24 : ((Zlength (person_x)) = k_pre)) (PreH25 : ((Zlength (person_y)) = k_pre)) (PreH26 : (Pre x_lines y_lines people )) (PreH27 : (StreetCoordinateBounds x_lines )) (PreH28 : (StreetCoordinateBounds y_lines )) (PreH29 : (PeopleCoordinateBounds people )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH31 : ((Zlength (vg)) = nv)) (PreH32 : ((Zlength (vk)) = nv)) (PreH33 : ((Zlength (hg)) = nh)) (PreH34 : ((Zlength (hk)) = nh)) (PreH35 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH36 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH37 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH38 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH39 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH40 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= nh) ” 
  &&  “ (nh <= k_pre) ”
).

Definition solver_partial_solve_wit_12_pure_split_goal_1 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (nh >= INT_MIN)) (PreH7 : (nv >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : ((Zlength (groups_after)) = nv)) (PreH12 : ((Zlength (keys_after)) = nv)) (PreH13 : (ParallelPermutation vg vk groups_after keys_after )) (PreH14 : (PairCountPrefix vg vk nv retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= m_pre)) (PreH18 : (m_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= 300000)) (PreH21 : (n_pre = (Zlength (x_lines)))) (PreH22 : (m_pre = (Zlength (y_lines)))) (PreH23 : (k_pre = (Zlength (people)))) (PreH24 : ((Zlength (person_x)) = k_pre)) (PreH25 : ((Zlength (person_y)) = k_pre)) (PreH26 : (Pre x_lines y_lines people )) (PreH27 : (StreetCoordinateBounds x_lines )) (PreH28 : (StreetCoordinateBounds y_lines )) (PreH29 : (PeopleCoordinateBounds people )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH31 : ((Zlength (vg)) = nv)) (PreH32 : ((Zlength (vk)) = nv)) (PreH33 : ((Zlength (hg)) = nh)) (PreH34 : ((Zlength (hk)) = nh)) (PreH35 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH36 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH37 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH38 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH39 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH40 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (0 <= nh) ”
.

Definition solver_partial_solve_wit_12_pure_split_goal_2 := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : (nh <= INT_MAX)) (PreH2 : (nv <= INT_MAX)) (PreH3 : (k_pre <= INT_MAX)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (nh >= INT_MIN)) (PreH7 : (nv >= INT_MIN)) (PreH8 : (k_pre >= INT_MIN)) (PreH9 : (m_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : ((Zlength (groups_after)) = nv)) (PreH12 : ((Zlength (keys_after)) = nv)) (PreH13 : (ParallelPermutation vg vk groups_after keys_after )) (PreH14 : (PairCountPrefix vg vk nv retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (2 <= m_pre)) (PreH18 : (m_pre <= 200000)) (PreH19 : (2 <= k_pre)) (PreH20 : (k_pre <= 300000)) (PreH21 : (n_pre = (Zlength (x_lines)))) (PreH22 : (m_pre = (Zlength (y_lines)))) (PreH23 : (k_pre = (Zlength (people)))) (PreH24 : ((Zlength (person_x)) = k_pre)) (PreH25 : ((Zlength (person_y)) = k_pre)) (PreH26 : (Pre x_lines y_lines people )) (PreH27 : (StreetCoordinateBounds x_lines )) (PreH28 : (StreetCoordinateBounds y_lines )) (PreH29 : (PeopleCoordinateBounds people )) (PreH30 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH31 : ((Zlength (vg)) = nv)) (PreH32 : ((Zlength (vk)) = nv)) (PreH33 : ((Zlength (hg)) = nh)) (PreH34 : ((Zlength (hk)) = nh)) (PreH35 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH36 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH37 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH38 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH39 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH40 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "ys" ) )) # Ptr  |-> ys_pre)
  **  ((( &( "px" ) )) # Ptr  |-> px_pre)
  **  ((( &( "py" ) )) # Ptr  |-> py_pre)
  **  ((( &( "va_grp" ) )) # Ptr  |-> va_grp_pre)
  **  ((( &( "va_key" ) )) # Ptr  |-> va_key_pre)
  **  ((( &( "ha_grp" ) )) # Ptr  |-> ha_grp_pre)
  **  ((( &( "ha_key" ) )) # Ptr  |-> ha_key_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "nv" ) )) # Int  |-> nv)
  **  ((( &( "nh" ) )) # Int  |-> nh)
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (nh <= k_pre) ”
.

Definition solver_partial_solve_wit_12_aux := 
forall (ha_key_pre: Z) (ha_grp_pre: Z) (va_key_pre: Z) (va_grp_pre: Z) (k_pre: Z) (py_pre: Z) (px_pre: Z) (m_pre: Z) (ys_pre: Z) (n_pre: Z) (xs_pre: Z) (person_y: (@list Z)) (person_x: (@list Z)) (people: (@list (Z * Z))) (y_lines: (@list Z)) (x_lines: (@list Z)) (vg: (@list Z)) (vk: (@list Z)) (hg: (@list Z)) (hk: (@list Z)) (vg_tail: (@list Z)) (vk_tail: (@list Z)) (hg_tail: (@list Z)) (hk_tail: (@list Z)) (nv: Z) (nh: Z) (keys_after: (@list Z)) (groups_after: (@list Z)) (retval: Z)  __default__Prod_Z_Z (PreH1 : ((Zlength (groups_after)) = nv)) (PreH2 : ((Zlength (keys_after)) = nv)) (PreH3 : (ParallelPermutation vg vk groups_after keys_after )) (PreH4 : (PairCountPrefix vg vk nv retval )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre <= 200000)) (PreH7 : (2 <= m_pre)) (PreH8 : (m_pre <= 200000)) (PreH9 : (2 <= k_pre)) (PreH10 : (k_pre <= 300000)) (PreH11 : (n_pre = (Zlength (x_lines)))) (PreH12 : (m_pre = (Zlength (y_lines)))) (PreH13 : (k_pre = (Zlength (people)))) (PreH14 : ((Zlength (person_x)) = k_pre)) (PreH15 : ((Zlength (person_y)) = k_pre)) (PreH16 : (Pre x_lines y_lines people )) (PreH17 : (StreetCoordinateBounds x_lines )) (PreH18 : (StreetCoordinateBounds y_lines )) (PreH19 : (PeopleCoordinateBounds people )) (PreH20 : forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z))))))) (PreH21 : ((Zlength (vg)) = nv)) (PreH22 : ((Zlength (vk)) = nv)) (PreH23 : ((Zlength (hg)) = nh)) (PreH24 : ((Zlength (hk)) = nh)) (PreH25 : ((Zlength (vg_tail)) = (k_pre - nv ))) (PreH26 : ((Zlength (vk_tail)) = (k_pre - nv ))) (PreH27 : ((Zlength (hg_tail)) = (k_pre - nh ))) (PreH28 : ((Zlength (hk_tail)) = (k_pre - nh ))) (PreH29 : (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk )) (PreH30 : (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk )) ,
  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
|--
  “ (k_pre <= 300000) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ (nh <= k_pre) ” 
  &&  “ (0 <= nh) ” 
  &&  “ ((Zlength (groups_after)) = nv) ” 
  &&  “ ((Zlength (keys_after)) = nv) ” 
  &&  “ (ParallelPermutation vg vk groups_after keys_after ) ” 
  &&  “ (PairCountPrefix vg vk nv retval ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= m_pre) ” 
  &&  “ (m_pre <= 200000) ” 
  &&  “ (2 <= k_pre) ” 
  &&  “ (k_pre <= 300000) ” 
  &&  “ (n_pre = (Zlength (x_lines))) ” 
  &&  “ (m_pre = (Zlength (y_lines))) ” 
  &&  “ (k_pre = (Zlength (people))) ” 
  &&  “ ((Zlength (person_x)) = k_pre) ” 
  &&  “ ((Zlength (person_y)) = k_pre) ” 
  &&  “ (Pre x_lines y_lines people ) ” 
  &&  “ (StreetCoordinateBounds x_lines ) ” 
  &&  “ (StreetCoordinateBounds y_lines ) ” 
  &&  “ (PeopleCoordinateBounds people ) ” 
  &&  “ forall (q: Z) , (((0 <= q) /\ (q < k_pre)) -> (((Znth q person_x 0) = (fst ((Znth q people __default__Prod_Z_Z)))) /\ ((Znth q person_y 0) = (snd ((Znth q people __default__Prod_Z_Z)))))) ” 
  &&  “ ((Zlength (vg)) = nv) ” 
  &&  “ ((Zlength (vk)) = nv) ” 
  &&  “ ((Zlength (hg)) = nh) ” 
  &&  “ ((Zlength (hk)) = nh) ” 
  &&  “ ((Zlength (vg_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (vk_tail)) = (k_pre - nv )) ” 
  &&  “ ((Zlength (hg_tail)) = (k_pre - nh )) ” 
  &&  “ ((Zlength (hk_tail)) = (k_pre - nh )) ” 
  &&  “ (ClassifiedPrefix x_lines y_lines people k_pre vg vk hg hk ) ” 
  &&  “ (ClassifiedCountsCorrect x_lines y_lines people k_pre vg vk hg hk ) ”
  &&  (IntArray.full ha_grp_pre nh hg )
  **  (IntArray.full ha_key_pre nh hk )
  **  (IntArray.full va_grp_pre nv groups_after )
  **  (IntArray.full va_key_pre nv keys_after )
  **  (IntArray.full xs_pre n_pre x_lines )
  **  (IntArray.full ys_pre m_pre y_lines )
  **  (IntArray.full px_pre k_pre person_x )
  **  (IntArray.full py_pre k_pre person_y )
  **  (IntArray.seg va_grp_pre nv k_pre vg_tail )
  **  (IntArray.seg va_key_pre nv k_pre vk_tail )
  **  (IntArray.seg ha_grp_pre nh k_pre hg_tail )
  **  (IntArray.seg ha_key_pre nh k_pre hk_tail )
.

Definition solver_partial_solve_wit_12 := solver_partial_solve_wit_12_pure -> solver_partial_solve_wit_12_aux.

Module Type VC_Correct.


Axiom proof_of_strip_safety_wit_1 : strip_safety_wit_1.
Axiom proof_of_strip_safety_wit_2 : strip_safety_wit_2.
Axiom proof_of_strip_safety_wit_3 : strip_safety_wit_3.
Axiom proof_of_strip_safety_wit_4 : strip_safety_wit_4.
Axiom proof_of_strip_safety_wit_5 : strip_safety_wit_5.
Axiom proof_of_strip_safety_wit_6 : strip_safety_wit_6.
Axiom proof_of_strip_safety_wit_7 : strip_safety_wit_7.
Axiom proof_of_strip_safety_wit_8 : strip_safety_wit_8.
Axiom proof_of_strip_safety_wit_9 : strip_safety_wit_9.
Axiom proof_of_strip_safety_wit_10 : strip_safety_wit_10.
Axiom proof_of_strip_safety_wit_11 : strip_safety_wit_11.
Axiom proof_of_strip_safety_wit_12 : strip_safety_wit_12.
Axiom proof_of_strip_safety_wit_13 : strip_safety_wit_13.
Axiom proof_of_strip_safety_wit_14 : strip_safety_wit_14.
Axiom proof_of_strip_safety_wit_15 : strip_safety_wit_15.
Axiom proof_of_strip_safety_wit_16 : strip_safety_wit_16.
Axiom proof_of_strip_safety_wit_17 : strip_safety_wit_17.
Axiom proof_of_strip_safety_wit_18 : strip_safety_wit_18.
Axiom proof_of_strip_safety_wit_19 : strip_safety_wit_19.
Axiom proof_of_strip_safety_wit_20 : strip_safety_wit_20.
Axiom proof_of_strip_safety_wit_21 : strip_safety_wit_21.
Axiom proof_of_strip_safety_wit_22 : strip_safety_wit_22.
Axiom proof_of_strip_safety_wit_23 : strip_safety_wit_23.
Axiom proof_of_strip_safety_wit_24 : strip_safety_wit_24.
Axiom proof_of_strip_safety_wit_25 : strip_safety_wit_25.
Axiom proof_of_strip_safety_wit_26 : strip_safety_wit_26.
Axiom proof_of_strip_safety_wit_27 : strip_safety_wit_27.
Axiom proof_of_strip_safety_wit_28 : strip_safety_wit_28.
Axiom proof_of_strip_safety_wit_29 : strip_safety_wit_29.
Axiom proof_of_strip_safety_wit_30 : strip_safety_wit_30.
Axiom proof_of_strip_safety_wit_31 : strip_safety_wit_31.
Axiom proof_of_strip_safety_wit_32 : strip_safety_wit_32.
Axiom proof_of_strip_safety_wit_33 : strip_safety_wit_33.
Axiom proof_of_strip_entail_wit_1 : strip_entail_wit_1.
Axiom proof_of_strip_entail_wit_2_1 : strip_entail_wit_2_1.
Axiom proof_of_strip_entail_wit_2_2 : strip_entail_wit_2_2.
Axiom proof_of_strip_entail_wit_2_3 : strip_entail_wit_2_3.
Axiom proof_of_strip_entail_wit_3_1 : strip_entail_wit_3_1.
Axiom proof_of_strip_entail_wit_3_2 : strip_entail_wit_3_2.
Axiom proof_of_strip_entail_wit_3_3 : strip_entail_wit_3_3.
Axiom proof_of_strip_entail_wit_3_4 : strip_entail_wit_3_4.
Axiom proof_of_strip_entail_wit_3_5 : strip_entail_wit_3_5.
Axiom proof_of_strip_entail_wit_3_6 : strip_entail_wit_3_6.
Axiom proof_of_strip_return_wit_1 : strip_return_wit_1.
Axiom proof_of_strip_return_wit_2 : strip_return_wit_2.
Axiom proof_of_strip_return_wit_3 : strip_return_wit_3.
Axiom proof_of_strip_return_wit_4 : strip_return_wit_4.
Axiom proof_of_strip_return_wit_5 : strip_return_wit_5.
Axiom proof_of_strip_return_wit_6 : strip_return_wit_6.
Axiom proof_of_strip_partial_solve_wit_1 : strip_partial_solve_wit_1.
Axiom proof_of_strip_partial_solve_wit_2 : strip_partial_solve_wit_2.
Axiom proof_of_strip_partial_solve_wit_3 : strip_partial_solve_wit_3.
Axiom proof_of_strip_partial_solve_wit_4 : strip_partial_solve_wit_4.
Axiom proof_of_strip_partial_solve_wit_5 : strip_partial_solve_wit_5.
Axiom proof_of_strip_partial_solve_wit_6 : strip_partial_solve_wit_6.
Axiom proof_of_item_less_return_wit_1 : item_less_return_wit_1.
Axiom proof_of_item_less_return_wit_2 : item_less_return_wit_2.
Axiom proof_of_item_less_return_wit_3 : item_less_return_wit_3.
Axiom proof_of_item_less_return_wit_4 : item_less_return_wit_4.
Axiom proof_of_sift_items_safety_wit_1 : sift_items_safety_wit_1.
Axiom proof_of_sift_items_safety_wit_2 : sift_items_safety_wit_2.
Axiom proof_of_sift_items_safety_wit_3 : sift_items_safety_wit_3.
Axiom proof_of_sift_items_safety_wit_4 : sift_items_safety_wit_4.
Axiom proof_of_sift_items_safety_wit_5 : sift_items_safety_wit_5.
Axiom proof_of_sift_items_safety_wit_6 : sift_items_safety_wit_6.
Axiom proof_of_sift_items_safety_wit_7 : sift_items_safety_wit_7.
Axiom proof_of_sift_items_safety_wit_8 : sift_items_safety_wit_8.
Axiom proof_of_sift_items_safety_wit_9 : sift_items_safety_wit_9.
Axiom proof_of_sift_items_safety_wit_10 : sift_items_safety_wit_10.
Axiom proof_of_sift_items_safety_wit_11 : sift_items_safety_wit_11.
Axiom proof_of_sift_items_safety_wit_12 : sift_items_safety_wit_12.
Axiom proof_of_sift_items_safety_wit_13 : sift_items_safety_wit_13.
Axiom proof_of_sift_items_safety_wit_14 : sift_items_safety_wit_14.
Axiom proof_of_sift_items_safety_wit_15 : sift_items_safety_wit_15.
Axiom proof_of_sift_items_safety_wit_16 : sift_items_safety_wit_16.
Axiom proof_of_sift_items_safety_wit_17 : sift_items_safety_wit_17.
Axiom proof_of_sift_items_safety_wit_18 : sift_items_safety_wit_18.
Axiom proof_of_sift_items_safety_wit_19 : sift_items_safety_wit_19.
Axiom proof_of_sift_items_safety_wit_20 : sift_items_safety_wit_20.
Axiom proof_of_sift_items_safety_wit_21 : sift_items_safety_wit_21.
Axiom proof_of_sift_items_safety_wit_22 : sift_items_safety_wit_22.
Axiom proof_of_sift_items_entail_wit_1 : sift_items_entail_wit_1.
Axiom proof_of_sift_items_entail_wit_2_1 : sift_items_entail_wit_2_1.
Axiom proof_of_sift_items_entail_wit_2_2 : sift_items_entail_wit_2_2.
Axiom proof_of_sift_items_entail_wit_2_3 : sift_items_entail_wit_2_3.
Axiom proof_of_sift_items_entail_wit_2_4 : sift_items_entail_wit_2_4.
Axiom proof_of_sift_items_entail_wit_3_1 : sift_items_entail_wit_3_1.
Axiom proof_of_sift_items_entail_wit_3_2 : sift_items_entail_wit_3_2.
Axiom proof_of_sift_items_entail_wit_3_3 : sift_items_entail_wit_3_3.
Axiom proof_of_sift_items_entail_wit_4_1 : sift_items_entail_wit_4_1.
Axiom proof_of_sift_items_entail_wit_4_2 : sift_items_entail_wit_4_2.
Axiom proof_of_sift_items_entail_wit_4_3 : sift_items_entail_wit_4_3.
Axiom proof_of_sift_items_entail_wit_4_4 : sift_items_entail_wit_4_4.
Axiom proof_of_sift_items_entail_wit_5_1 : sift_items_entail_wit_5_1.
Axiom proof_of_sift_items_entail_wit_5_2 : sift_items_entail_wit_5_2.
Axiom proof_of_sift_items_entail_wit_6 : sift_items_entail_wit_6.
Axiom proof_of_sift_items_return_wit_1 : sift_items_return_wit_1.
Axiom proof_of_sift_items_return_wit_2 : sift_items_return_wit_2.
Axiom proof_of_sift_items_partial_solve_wit_1 : sift_items_partial_solve_wit_1.
Axiom proof_of_sift_items_partial_solve_wit_2 : sift_items_partial_solve_wit_2.
Axiom proof_of_sift_items_partial_solve_wit_3 : sift_items_partial_solve_wit_3.
Axiom proof_of_sift_items_partial_solve_wit_4 : sift_items_partial_solve_wit_4.
Axiom proof_of_sift_items_partial_solve_wit_5 : sift_items_partial_solve_wit_5.
Axiom proof_of_sift_items_partial_solve_wit_6 : sift_items_partial_solve_wit_6.
Axiom proof_of_sift_items_partial_solve_wit_7 : sift_items_partial_solve_wit_7.
Axiom proof_of_sift_items_partial_solve_wit_8 : sift_items_partial_solve_wit_8.
Axiom proof_of_sift_items_partial_solve_wit_9 : sift_items_partial_solve_wit_9.
Axiom proof_of_sift_items_partial_solve_wit_10 : sift_items_partial_solve_wit_10.
Axiom proof_of_sift_items_partial_solve_wit_11 : sift_items_partial_solve_wit_11.
Axiom proof_of_sift_items_partial_solve_wit_12 : sift_items_partial_solve_wit_12.
Axiom proof_of_sift_items_partial_solve_wit_13 : sift_items_partial_solve_wit_13.
Axiom proof_of_sift_items_partial_solve_wit_14 : sift_items_partial_solve_wit_14.
Axiom proof_of_sift_items_partial_solve_wit_15 : sift_items_partial_solve_wit_15.
Axiom proof_of_sift_items_partial_solve_wit_16 : sift_items_partial_solve_wit_16.
Axiom proof_of_sift_items_partial_solve_wit_17 : sift_items_partial_solve_wit_17.
Axiom proof_of_sift_items_partial_solve_wit_18 : sift_items_partial_solve_wit_18.
Axiom proof_of_sift_items_partial_solve_wit_19 : sift_items_partial_solve_wit_19.
Axiom proof_of_sift_items_partial_solve_wit_20 : sift_items_partial_solve_wit_20.
Axiom proof_of_sift_items_partial_solve_wit_21 : sift_items_partial_solve_wit_21.
Axiom proof_of_sift_items_partial_solve_wit_22 : sift_items_partial_solve_wit_22.
Axiom proof_of_sift_items_partial_solve_wit_23 : sift_items_partial_solve_wit_23.
Axiom proof_of_sift_items_partial_solve_wit_24 : sift_items_partial_solve_wit_24.
Axiom proof_of_sift_items_partial_solve_wit_25 : sift_items_partial_solve_wit_25.
Axiom proof_of_sift_items_partial_solve_wit_26 : sift_items_partial_solve_wit_26.
Axiom proof_of_sort_items_safety_wit_1 : sort_items_safety_wit_1.
Axiom proof_of_sort_items_safety_wit_2 : sort_items_safety_wit_2.
Axiom proof_of_sort_items_safety_wit_3 : sort_items_safety_wit_3.
Axiom proof_of_sort_items_safety_wit_4 : sort_items_safety_wit_4.
Axiom proof_of_sort_items_safety_wit_5 : sort_items_safety_wit_5.
Axiom proof_of_sort_items_safety_wit_6 : sort_items_safety_wit_6.
Axiom proof_of_sort_items_safety_wit_7 : sort_items_safety_wit_7.
Axiom proof_of_sort_items_safety_wit_8 : sort_items_safety_wit_8.
Axiom proof_of_sort_items_safety_wit_9 : sort_items_safety_wit_9.
Axiom proof_of_sort_items_safety_wit_10 : sort_items_safety_wit_10.
Axiom proof_of_sort_items_safety_wit_11 : sort_items_safety_wit_11.
Axiom proof_of_sort_items_safety_wit_12 : sort_items_safety_wit_12.
Axiom proof_of_sort_items_safety_wit_13 : sort_items_safety_wit_13.
Axiom proof_of_sort_items_safety_wit_14 : sort_items_safety_wit_14.
Axiom proof_of_sort_items_safety_wit_15 : sort_items_safety_wit_15.
Axiom proof_of_sort_items_safety_wit_16 : sort_items_safety_wit_16.
Axiom proof_of_sort_items_safety_wit_17 : sort_items_safety_wit_17.
Axiom proof_of_sort_items_safety_wit_18 : sort_items_safety_wit_18.
Axiom proof_of_sort_items_safety_wit_19 : sort_items_safety_wit_19.
Axiom proof_of_sort_items_entail_wit_1 : sort_items_entail_wit_1.
Axiom proof_of_sort_items_entail_wit_2 : sort_items_entail_wit_2.
Axiom proof_of_sort_items_entail_wit_3 : sort_items_entail_wit_3.
Axiom proof_of_sort_items_entail_wit_4 : sort_items_entail_wit_4.
Axiom proof_of_sort_items_entail_wit_5 : sort_items_entail_wit_5.
Axiom proof_of_sort_items_return_wit_1 : sort_items_return_wit_1.
Axiom proof_of_sort_items_partial_solve_wit_1_pure : sort_items_partial_solve_wit_1_pure.
Axiom proof_of_sort_items_partial_solve_wit_1 : sort_items_partial_solve_wit_1.
Axiom proof_of_sort_items_partial_solve_wit_2 : sort_items_partial_solve_wit_2.
Axiom proof_of_sort_items_partial_solve_wit_3 : sort_items_partial_solve_wit_3.
Axiom proof_of_sort_items_partial_solve_wit_4 : sort_items_partial_solve_wit_4.
Axiom proof_of_sort_items_partial_solve_wit_5 : sort_items_partial_solve_wit_5.
Axiom proof_of_sort_items_partial_solve_wit_6 : sort_items_partial_solve_wit_6.
Axiom proof_of_sort_items_partial_solve_wit_7 : sort_items_partial_solve_wit_7.
Axiom proof_of_sort_items_partial_solve_wit_8 : sort_items_partial_solve_wit_8.
Axiom proof_of_sort_items_partial_solve_wit_9 : sort_items_partial_solve_wit_9.
Axiom proof_of_sort_items_partial_solve_wit_10_pure : sort_items_partial_solve_wit_10_pure.
Axiom proof_of_sort_items_partial_solve_wit_10 : sort_items_partial_solve_wit_10.
Axiom proof_of_count_pairs_safety_wit_1 : count_pairs_safety_wit_1.
Axiom proof_of_count_pairs_safety_wit_2 : count_pairs_safety_wit_2.
Axiom proof_of_count_pairs_safety_wit_3 : count_pairs_safety_wit_3.
Axiom proof_of_count_pairs_safety_wit_4 : count_pairs_safety_wit_4.
Axiom proof_of_count_pairs_safety_wit_5 : count_pairs_safety_wit_5.
Axiom proof_of_count_pairs_safety_wit_6 : count_pairs_safety_wit_6.
Axiom proof_of_count_pairs_safety_wit_7 : count_pairs_safety_wit_7.
Axiom proof_of_count_pairs_safety_wit_8 : count_pairs_safety_wit_8.
Axiom proof_of_count_pairs_safety_wit_9 : count_pairs_safety_wit_9.
Axiom proof_of_count_pairs_safety_wit_10 : count_pairs_safety_wit_10.
Axiom proof_of_count_pairs_safety_wit_11 : count_pairs_safety_wit_11.
Axiom proof_of_count_pairs_safety_wit_12 : count_pairs_safety_wit_12.
Axiom proof_of_count_pairs_safety_wit_13 : count_pairs_safety_wit_13.
Axiom proof_of_count_pairs_safety_wit_14 : count_pairs_safety_wit_14.
Axiom proof_of_count_pairs_safety_wit_15 : count_pairs_safety_wit_15.
Axiom proof_of_count_pairs_safety_wit_16 : count_pairs_safety_wit_16.
Axiom proof_of_count_pairs_safety_wit_17 : count_pairs_safety_wit_17.
Axiom proof_of_count_pairs_safety_wit_18 : count_pairs_safety_wit_18.
Axiom proof_of_count_pairs_safety_wit_19 : count_pairs_safety_wit_19.
Axiom proof_of_count_pairs_safety_wit_20 : count_pairs_safety_wit_20.
Axiom proof_of_count_pairs_safety_wit_21 : count_pairs_safety_wit_21.
Axiom proof_of_count_pairs_safety_wit_22 : count_pairs_safety_wit_22.
Axiom proof_of_count_pairs_safety_wit_23 : count_pairs_safety_wit_23.
Axiom proof_of_count_pairs_safety_wit_24 : count_pairs_safety_wit_24.
Axiom proof_of_count_pairs_safety_wit_25 : count_pairs_safety_wit_25.
Axiom proof_of_count_pairs_safety_wit_26 : count_pairs_safety_wit_26.
Axiom proof_of_count_pairs_safety_wit_27 : count_pairs_safety_wit_27.
Axiom proof_of_count_pairs_safety_wit_28 : count_pairs_safety_wit_28.
Axiom proof_of_count_pairs_safety_wit_29 : count_pairs_safety_wit_29.
Axiom proof_of_count_pairs_safety_wit_30 : count_pairs_safety_wit_30.
Axiom proof_of_count_pairs_safety_wit_31 : count_pairs_safety_wit_31.
Axiom proof_of_count_pairs_safety_wit_32 : count_pairs_safety_wit_32.
Axiom proof_of_count_pairs_safety_wit_33 : count_pairs_safety_wit_33.
Axiom proof_of_count_pairs_safety_wit_34 : count_pairs_safety_wit_34.
Axiom proof_of_count_pairs_entail_wit_1 : count_pairs_entail_wit_1.
Axiom proof_of_count_pairs_entail_wit_2 : count_pairs_entail_wit_2.
Axiom proof_of_count_pairs_entail_wit_3 : count_pairs_entail_wit_3.
Axiom proof_of_count_pairs_entail_wit_4_1 : count_pairs_entail_wit_4_1.
Axiom proof_of_count_pairs_entail_wit_4_2 : count_pairs_entail_wit_4_2.
Axiom proof_of_count_pairs_entail_wit_5 : count_pairs_entail_wit_5.
Axiom proof_of_count_pairs_entail_wit_6 : count_pairs_entail_wit_6.
Axiom proof_of_count_pairs_entail_wit_7_1 : count_pairs_entail_wit_7_1.
Axiom proof_of_count_pairs_entail_wit_7_2 : count_pairs_entail_wit_7_2.
Axiom proof_of_count_pairs_entail_wit_8 : count_pairs_entail_wit_8.
Axiom proof_of_count_pairs_return_wit_1 : count_pairs_return_wit_1.
Axiom proof_of_count_pairs_partial_solve_wit_1_pure : count_pairs_partial_solve_wit_1_pure.
Axiom proof_of_count_pairs_partial_solve_wit_1 : count_pairs_partial_solve_wit_1.
Axiom proof_of_count_pairs_partial_solve_wit_2 : count_pairs_partial_solve_wit_2.
Axiom proof_of_count_pairs_partial_solve_wit_3 : count_pairs_partial_solve_wit_3.
Axiom proof_of_count_pairs_partial_solve_wit_4 : count_pairs_partial_solve_wit_4.
Axiom proof_of_count_pairs_partial_solve_wit_5 : count_pairs_partial_solve_wit_5.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.

End VC_Correct.
