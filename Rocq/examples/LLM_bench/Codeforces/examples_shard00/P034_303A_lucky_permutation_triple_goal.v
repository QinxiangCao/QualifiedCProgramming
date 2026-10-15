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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P034_303A_lucky_permutation_triple_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre (3 * n_pre ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre (3 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : ((Z.land n_pre 1) = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre (3 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre (3 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (a) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) (3 * n_pre ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (a: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg out_pre 0 i a )
  **  (IntArray.undef_seg out_pre i (3 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange i b )) ,
  (IntArray.seg out_pre n_pre ((n_pre + i ) + 1 ) (app (b) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((n_pre + i ) + 1 ) (3 * n_pre ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange i b )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (n_pre + i ) b )
  **  (IntArray.undef_seg out_pre (n_pre + i ) (3 * n_pre ) )
|--
  “ ((n_pre + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + i )) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange i b )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (n_pre + i ) b )
  **  (IntArray.undef_seg out_pre (n_pre + i ) (3 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  (IntArray.seg out_pre (2 * n_pre ) (((2 * n_pre ) + i ) + 1 ) (app (c) ((cons (((2 * i ) % ( n_pre ) )) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (((2 * n_pre ) + i ) + 1 ) (3 * n_pre ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ (((2 * n_pre ) + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * n_pre ) + i )) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ (((2 * i ) <> (INT_MIN)) \/ (n_pre <> (-1))) ” 
  &&  “ (n_pre <> 0) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (IntArray.undef_full out_pre (3 * n_pre ) )
|--
  EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (IdentityRange 0 a ) ”
  &&  (IntArray.seg out_pre 0 0 a )
  **  (IntArray.undef_seg out_pre 0 (3 * n_pre ) )
) \/
(
forall (n_pre: Z) (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  TT && emp 
|--
  “ (IdentityRange 0 (@nil Z) ) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (IdentityRange 0 (@nil Z) )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (PreH1 : ((Z.land n_pre 1) <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  ((n_pre % ( 2 ) ) = 1)
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (a_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a_2 )) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (a_2) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) (3 * n_pre ) )
|--
  EX (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (IdentityRange (i + 1 ) a ) ”
  &&  (IntArray.seg out_pre 0 (i + 1 ) a )
  **  (IntArray.undef_seg out_pre (i + 1 ) (3 * n_pre ) )
) \/
(
forall (n_pre: Z) (a_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a_2 )) ,
  TT && emp 
|--
  “ (IdentityRange (i + 1 ) (app (a_2) ((cons (i) ((@nil Z))))) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (a_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a_2 )) ,
  (IdentityRange (i + 1 ) (app (a_2) ((cons (i) ((@nil Z))))) )
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (n_pre: Z) (a_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a_2 )) ,
  (IntArray.seg out_pre 0 i a_2 )
  **  (IntArray.undef_seg out_pre i (3 * n_pre ) )
|--
  EX (b: (@list Z))  (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (IdentityRange n_pre a ) ” 
  &&  “ (IdentityRange 0 b ) ”
  &&  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (n_pre + 0 ) b )
  **  (IntArray.undef_seg out_pre (n_pre + 0 ) (3 * n_pre ) )
) \/
(
forall (out_pre: Z) (n_pre: Z) (a_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a_2 )) ,
  (IntArray.seg out_pre 0 i a_2 )
|--
  EX (b: (@list Z))  (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (IdentityRange n_pre a ) ” 
  &&  “ (IdentityRange 0 b ) ”
  &&  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (n_pre + 0 ) b )
).

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (n_pre: Z) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange i b_2 )) ,
  (IntArray.seg out_pre n_pre ((n_pre + i ) + 1 ) (app (b_2) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((n_pre + i ) + 1 ) (3 * n_pre ) )
  **  (IntArray.seg out_pre 0 n_pre a_2 )
|--
  EX (b: (@list Z))  (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (IdentityRange n_pre a ) ” 
  &&  “ (IdentityRange (i + 1 ) b ) ”
  &&  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (n_pre + (i + 1 ) ) b )
  **  (IntArray.undef_seg out_pre (n_pre + (i + 1 ) ) (3 * n_pre ) )
) \/
(
forall (out_pre: Z) (n_pre: Z) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange i b_2 )) ,
  (IntArray.seg out_pre n_pre ((n_pre + i ) + 1 ) (app (b_2) ((cons (i) ((@nil Z))))) )
|--
  EX (b: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (IdentityRange n_pre a_2 ) ” 
  &&  “ (IdentityRange (i + 1 ) b ) ”
  &&  (IntArray.seg out_pre n_pre (n_pre + (i + 1 ) ) b )
).

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (n_pre: Z) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange i b_2 )) ,
  (IntArray.seg out_pre 0 n_pre a_2 )
  **  (IntArray.seg out_pre n_pre (n_pre + i ) b_2 )
  **  (IntArray.undef_seg out_pre (n_pre + i ) (3 * n_pre ) )
|--
  EX (c: (@list Z))  (b: (@list Z))  (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (IdentityRange n_pre a ) ” 
  &&  “ (IdentityRange n_pre b ) ” 
  &&  “ (TwiceModRange n_pre 0 c ) ”
  &&  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + 0 ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + 0 ) (3 * n_pre ) )
) \/
(
forall (out_pre: Z) (n_pre: Z) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange i b_2 )) ,
  (IntArray.seg out_pre n_pre (n_pre + i ) b_2 )
|--
  EX (c: (@list Z))  (b: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (IdentityRange n_pre a_2 ) ” 
  &&  “ (IdentityRange n_pre b ) ” 
  &&  “ (TwiceModRange n_pre 0 c ) ”
  &&  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + 0 ) c )
).

Definition solver_entail_wit_6 := 
(
forall (out_pre: Z) (n_pre: Z) (c_2: (@list Z)) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange n_pre b_2 )) (PreH9 : (TwiceModRange n_pre i c_2 )) ,
  (IntArray.seg out_pre (2 * n_pre ) (((2 * n_pre ) + i ) + 1 ) (app (c_2) ((cons (((2 * i ) % ( n_pre ) )) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (((2 * n_pre ) + i ) + 1 ) (3 * n_pre ) )
  **  (IntArray.seg out_pre 0 n_pre a_2 )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b_2 )
|--
  EX (c: (@list Z))  (b: (@list Z))  (a: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (IdentityRange n_pre a ) ” 
  &&  “ (IdentityRange n_pre b ) ” 
  &&  “ (TwiceModRange n_pre (i + 1 ) c ) ”
  &&  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + (i + 1 ) ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + (i + 1 ) ) (3 * n_pre ) )
) \/
(
forall (out_pre: Z) (n_pre: Z) (c_2: (@list Z)) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange n_pre b_2 )) (PreH9 : (TwiceModRange n_pre i c_2 )) ,
  (IntArray.seg out_pre (2 * n_pre ) (((2 * n_pre ) + i ) + 1 ) (app (c_2) ((cons (((2 * i ) % ( n_pre ) )) ((@nil Z))))) )
|--
  EX (c: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (IdentityRange n_pre a_2 ) ” 
  &&  “ (IdentityRange n_pre b_2 ) ” 
  &&  “ (TwiceModRange n_pre (i + 1 ) c ) ”
  &&  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + (i + 1 ) ) c )
).

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (c_2: (@list Z)) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange n_pre b_2 )) (PreH9 : (TwiceModRange n_pre i c_2 )) ,
  (IntArray.seg out_pre 0 n_pre a_2 )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b_2 )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c_2 )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  EX (a: (@list Z))  (b: (@list Z))  (c: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (Spec n_pre (Some ((pair ((pair (a) (b))) (c)))) ) ”
  &&  (IntArray.full out_pre (3 * n_pre ) (app (a) ((app (b) (c)))) )
) \/
(
forall (out_pre: Z) (n_pre: Z) (c_2: (@list Z)) (b_2: (@list Z)) (a_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a_2 )) (PreH8 : (IdentityRange n_pre b_2 )) (PreH9 : (TwiceModRange n_pre i c_2 )) ,
  (IntArray.seg out_pre 0 n_pre a_2 )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b_2 )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c_2 )
|--
  EX (a: (@list Z))  (b: (@list Z))  (c: (@list Z)) ,
  “ (Spec n_pre (Some ((pair ((pair (a) (b))) (c)))) ) ”
  &&  (IntArray.full out_pre (3 * n_pre ) (app (a) ((app (b) (c)))) )
).

Definition solver_return_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (PreH1 : ((Z.land n_pre 1) = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (IntArray.undef_full out_pre (3 * n_pre ) )
|--
  “ (0 = 0) ” 
  &&  “ (Spec n_pre None ) ”
  &&  (IntArray.undef_full out_pre (3 * n_pre ) )
) \/
(
forall (n_pre: Z) (PreH1 : ((Z.land n_pre 1) = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec n_pre None ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (PreH1 : ((Z.land n_pre 1) = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) ,
  (Spec n_pre None )
.

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange i a )) ,
  (IntArray.seg out_pre 0 i a )
  **  (IntArray.undef_seg out_pre i (3 * n_pre ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (IdentityRange i a ) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) (3 * n_pre ) )
  **  (IntArray.seg out_pre 0 i a )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange i b )) ,
  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (n_pre + i ) b )
  **  (IntArray.undef_seg out_pre (n_pre + i ) (3 * n_pre ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (IdentityRange n_pre a ) ” 
  &&  “ (IdentityRange i b ) ”
  &&  (((out_pre + ((n_pre + i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre ((n_pre + i ) + 1 ) (3 * n_pre ) )
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (n_pre + i ) b )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((n_pre % ( 2 ) ) = 1)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (IdentityRange n_pre a )) (PreH8 : (IdentityRange n_pre b )) (PreH9 : (TwiceModRange n_pre i c )) ,
  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
  **  (IntArray.undef_seg out_pre ((2 * n_pre ) + i ) (3 * n_pre ) )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((n_pre % ( 2 ) ) = 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (IdentityRange n_pre a ) ” 
  &&  “ (IdentityRange n_pre b ) ” 
  &&  “ (TwiceModRange n_pre i c ) ”
  &&  (((out_pre + (((2 * n_pre ) + i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (((2 * n_pre ) + i ) + 1 ) (3 * n_pre ) )
  **  (IntArray.seg out_pre 0 n_pre a )
  **  (IntArray.seg out_pre n_pre (2 * n_pre ) b )
  **  (IntArray.seg out_pre (2 * n_pre ) ((2 * n_pre ) + i ) c )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
