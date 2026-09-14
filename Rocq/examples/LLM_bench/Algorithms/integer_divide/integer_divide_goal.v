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
Require Import SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_lib.
Local Open Scope sac.

(*----- Function divide -----*)

Definition divide_safety_wit_1 := 
forall (p_pre: Z) (n_pre: Z) (original: Z) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  ((( &( "cnt" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (IntArray.undef_full p_pre original )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition divide_safety_wit_2 := 
forall (p_pre: Z) (n_pre: Z) (original: Z) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (IntArray.undef_full p_pre original )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition divide_safety_wit_3 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (i <= n)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ ((n <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition divide_safety_wit_4 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (n = 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ ((n <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition divide_safety_wit_5 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (n = 1)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition divide_safety_wit_6 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (i <= n)) (PreH8 : (0 <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition divide_safety_wit_7 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i )) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ ((cnt + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition divide_safety_wit_8 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i )) ,
  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ ((cnt + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition divide_safety_wit_9 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i )) ,
  (IntArray.seg p_pre 1 ((1 + cnt ) + 1 ) (app (factors) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg p_pre ((1 + cnt ) + 1 ) original )
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg p_pre 0 1 )
|--
  “ ((n <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition divide_safety_wit_10 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i )) ,
  (IntArray.seg p_pre 1 ((1 + cnt ) + 1 ) (app (factors) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg p_pre ((1 + cnt ) + 1 ) original )
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg p_pre 0 1 )
|--
  “ ((n <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition divide_safety_wit_11 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((n % ( i ) ) <> 0)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= original)) (PreH8 : (n = 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors)) = cnt)) (PreH12 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition divide_safety_wit_12 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((n % ( i ) ) <> 0)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= original)) (PreH8 : (i <= n)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors)) = cnt)) (PreH12 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition divide_safety_wit_13 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (n <> 1)) (PreH2 : ((n % ( i ) ) <> 0)) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (n = 1)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors)) = cnt)) (PreH13 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ False ”
.

Definition divide_safety_wit_14 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (n = 1)) (PreH2 : ((n % ( i ) ) <> 0)) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (i <= n)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors)) = cnt)) (PreH13 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ False ”
.

Definition divide_safety_wit_15 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n <> 1)) (PreH7 : ((n % ( i ) ) <> 0)) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors)) = cnt)) (PreH18 : (FactorizationProgress original factors n i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition divide_entail_wit_1 := 
(
forall (p_pre: Z) (n_pre: Z) (original: Z) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  (IntArray.undef_full p_pre original )
|--
  EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= original) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= INT_MAX) ” 
  &&  “ (2 <= (original + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < original) ” 
  &&  “ ((Zlength (factors)) = 0) ” 
  &&  “ (FactorizationProgress original factors n_pre 2 ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + 0 ) factors )
  **  (IntArray.undef_seg p_pre (1 + 0 ) original )
) \/
(
forall (p_pre: Z) (n_pre: Z) (original: Z) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  (IntArray.undef_full p_pre original )
|--
  EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= original) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= INT_MAX) ” 
  &&  “ (2 <= (original + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < original) ” 
  &&  “ ((Zlength (factors)) = 0) ” 
  &&  “ (FactorizationProgress original factors n_pre 2 ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + 0 ) factors )
  **  (IntArray.undef_seg p_pre (1 + 0 ) original )
).

Definition divide_entail_wit_2 := 
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (i <= n)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= INT_MAX)) (PreH8 : (i <= (original + 1 ))) (PreH9 : (0 <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors_2)) = cnt)) (PreH12 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt < original) ” 
  &&  “ ((Zlength (factors)) = cnt) ” 
  &&  “ (FactorizationProgress original factors n i ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
.

Definition divide_entail_wit_3_1 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((n % ( i ) ) = 0)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= original)) (PreH8 : (n = 1)) (PreH9 : (0 <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors)) = cnt)) (PreH12 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  (“ ((cnt + 1 ) < original) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n >= INT_MIN) ” 
  &&  “ ((n % ( i ) ) = 0) ” 
  &&  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (n = 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt < original) ” 
  &&  “ ((Zlength (factors)) = cnt) ” 
  &&  “ (FactorizationProgress original factors n i ) ”
  &&  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original ))
  ||
  (EX (factors_2: (@list Z))  (cnt_2: Z)  (i_2: Z)  (n_2: Z) ,
  “ ((cnt_2 + 1 ) < original) ” 
  &&  “ (i_2 <= INT_MAX) ” 
  &&  “ (n_2 <= INT_MAX) ” 
  &&  “ (i_2 >= INT_MIN) ” 
  &&  “ (n_2 >= INT_MIN) ” 
  &&  “ ((n_2 % ( i_2 ) ) = 0) ” 
  &&  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n_2) ” 
  &&  “ (n_2 <= original) ” 
  &&  “ (2 <= i_2) ” 
  &&  “ (i_2 <= original) ” 
  &&  “ (i_2 <= n_2) ” 
  &&  “ (0 <= cnt_2) ” 
  &&  “ (cnt_2 < original) ” 
  &&  “ ((Zlength (factors_2)) = cnt_2) ” 
  &&  “ (FactorizationProgress original factors_2 n_2 i_2 ) ”
  &&  ((( &( "cnt" ) )) # Int  |-> cnt_2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt_2 ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt_2 ) original ))
.

Definition divide_entail_wit_3_2 := 
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt_2: Z) (i_2: Z) (n_2: Z) (PreH1 : ((n_2 % ( i_2 ) ) = 0)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n_2)) (PreH5 : (n_2 <= original)) (PreH6 : (2 <= i_2)) (PreH7 : (i_2 <= original)) (PreH8 : (i_2 <= n_2)) (PreH9 : (0 <= cnt_2)) (PreH10 : (cnt_2 < original)) (PreH11 : ((Zlength (factors_2)) = cnt_2)) (PreH12 : (FactorizationProgress original factors_2 n_2 i_2 )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "cnt" ) )) # Int  |-> cnt_2)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt_2 ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt_2 ) original )
|--
  (EX (factors: (@list Z))  (cnt: Z)  (i: Z)  (n: Z) ,
  “ ((cnt + 1 ) < original) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n >= INT_MIN) ” 
  &&  “ ((n % ( i ) ) = 0) ” 
  &&  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (n = 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt < original) ” 
  &&  “ ((Zlength (factors)) = cnt) ” 
  &&  “ (FactorizationProgress original factors n i ) ”
  &&  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original ))
  ||
  (“ ((cnt_2 + 1 ) < original) ” 
  &&  “ (i_2 <= INT_MAX) ” 
  &&  “ (n_2 <= INT_MAX) ” 
  &&  “ (i_2 >= INT_MIN) ” 
  &&  “ (n_2 >= INT_MIN) ” 
  &&  “ ((n_2 % ( i_2 ) ) = 0) ” 
  &&  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n_2) ” 
  &&  “ (n_2 <= original) ” 
  &&  “ (2 <= i_2) ” 
  &&  “ (i_2 <= original) ” 
  &&  “ (i_2 <= n_2) ” 
  &&  “ (0 <= cnt_2) ” 
  &&  “ (cnt_2 < original) ” 
  &&  “ ((Zlength (factors_2)) = cnt_2) ” 
  &&  “ (FactorizationProgress original factors_2 n_2 i_2 ) ”
  &&  ((( &( "cnt" ) )) # Int  |-> cnt_2)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt_2 ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt_2 ) original ))
.

Definition divide_entail_wit_4_1 := 
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors_2)) = cnt)) (PreH17 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.seg p_pre 1 ((1 + cnt ) + 1 ) (app (factors_2) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg p_pre ((1 + cnt ) + 1 ) original )
  **  (IntArray.undef_seg p_pre 0 1 )
|--
  (EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= (n ÷ i )) ” 
  &&  “ ((n ÷ i ) <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ ((n ÷ i ) = 1) ” 
  &&  “ (0 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) < original) ” 
  &&  “ ((Zlength (factors)) = (cnt + 1 )) ” 
  &&  “ (FactorizationProgress original factors (n ÷ i ) i ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + (cnt + 1 ) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (cnt + 1 ) ) original ))
  ||
  (EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= (n ÷ i )) ” 
  &&  “ ((n ÷ i ) <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (i <= (n ÷ i )) ” 
  &&  “ (0 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) < original) ” 
  &&  “ ((Zlength (factors)) = (cnt + 1 )) ” 
  &&  “ (FactorizationProgress original factors (n ÷ i ) i ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + (cnt + 1 ) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (cnt + 1 ) ) original ))
.

Definition divide_entail_wit_4_2 := 
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors_2)) = cnt)) (PreH17 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.seg p_pre 1 ((1 + cnt ) + 1 ) (app (factors_2) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg p_pre ((1 + cnt ) + 1 ) original )
  **  (IntArray.undef_seg p_pre 0 1 )
|--
  (EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= (n ÷ i )) ” 
  &&  “ ((n ÷ i ) <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ ((n ÷ i ) = 1) ” 
  &&  “ (0 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) < original) ” 
  &&  “ ((Zlength (factors)) = (cnt + 1 )) ” 
  &&  “ (FactorizationProgress original factors (n ÷ i ) i ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + (cnt + 1 ) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (cnt + 1 ) ) original ))
  ||
  (EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= (n ÷ i )) ” 
  &&  “ ((n ÷ i ) <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (i <= (n ÷ i )) ” 
  &&  “ (0 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) < original) ” 
  &&  “ ((Zlength (factors)) = (cnt + 1 )) ” 
  &&  “ (FactorizationProgress original factors (n ÷ i ) i ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + (cnt + 1 ) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (cnt + 1 ) ) original ))
.

Definition divide_entail_wit_5 := 
(
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (n <> 1)) (PreH2 : ((n % ( i ) ) <> 0)) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (i <= n)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors)) = cnt)) (PreH13 : (FactorizationProgress original factors n i )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ (i < INT_MAX) ” 
  &&  “ (cnt <= INT_MAX) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (cnt >= INT_MIN) ” 
  &&  “ (n >= INT_MIN) ” 
  &&  “ (n <> 1) ” 
  &&  “ ((n % ( i ) ) <> 0) ” 
  &&  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt < original) ” 
  &&  “ ((Zlength (factors)) = cnt) ” 
  &&  “ (FactorizationProgress original factors n i ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
) \/
(
forall (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n >= INT_MIN)) (PreH7 : (n <> 1)) (PreH8 : ((n % ( i ) ) <> 0)) (PreH9 : (1 <= original)) (PreH10 : (original <= INT_MAX)) (PreH11 : (1 <= n)) (PreH12 : (n <= original)) (PreH13 : (2 <= i)) (PreH14 : (i <= original)) (PreH15 : (i <= n)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt < original)) (PreH18 : ((Zlength (factors)) = cnt)) (PreH19 : (FactorizationProgress original factors n i )) ,
  TT && emp 
|--
  “ (i < INT_MAX) ”
  &&  emp
).

Definition divide_entail_wit_5_split_goal_1 := 
forall (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n >= INT_MIN)) (PreH7 : (n <> 1)) (PreH8 : ((n % ( i ) ) <> 0)) (PreH9 : (1 <= original)) (PreH10 : (original <= INT_MAX)) (PreH11 : (1 <= n)) (PreH12 : (n <= original)) (PreH13 : (2 <= i)) (PreH14 : (i <= original)) (PreH15 : (i <= n)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt < original)) (PreH18 : ((Zlength (factors)) = cnt)) (PreH19 : (FactorizationProgress original factors n i )) ,
  (i < INT_MAX)
.

Definition divide_entail_wit_6 := 
(
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n <> 1)) (PreH7 : ((n % ( i ) ) <> 0)) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors_2)) = cnt)) (PreH18 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  EX (factors: (@list Z)) ,
  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= original) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((i + 1 ) <= (original + 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt < original) ” 
  &&  “ ((Zlength (factors)) = cnt) ” 
  &&  “ (FactorizationProgress original factors n (i + 1 ) ) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
) \/
(
forall (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n <> 1)) (PreH7 : ((n % ( i ) ) <> 0)) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors_2)) = cnt)) (PreH18 : (FactorizationProgress original factors_2 n i )) ,
  TT && emp 
|--
  “ (FactorizationProgress original factors_2 n (i + 1 ) ) ”
  &&  emp
).

Definition divide_entail_wit_6_split_goal_1 := 
forall (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n <> 1)) (PreH7 : ((n % ( i ) ) <> 0)) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors_2)) = cnt)) (PreH18 : (FactorizationProgress original factors_2 n i )) ,
  (FactorizationProgress original factors_2 n (i + 1 ) )
.

Definition divide_return_wit_1 := 
(
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (i > n)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= INT_MAX)) (PreH8 : (i <= (original + 1 ))) (PreH9 : (0 <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors_2)) = cnt)) (PreH12 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  EX (factors: (@list Z)) ,
  “ (PrimeFactorization original factors ) ” 
  &&  “ ((Zlength (factors)) < original) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + (Zlength (factors)) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (Zlength (factors)) ) original )
) \/
(
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (i > n)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= INT_MAX)) (PreH8 : (i <= (original + 1 ))) (PreH9 : (0 <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors_2)) = cnt)) (PreH12 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.seg p_pre 1 (1 + cnt ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  EX (factors: (@list Z)) ,
  “ (PrimeFactorization original factors ) ” 
  &&  “ ((Zlength (factors)) < original) ”
  &&  (IntArray.seg p_pre 1 (1 + (Zlength (factors)) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (Zlength (factors)) ) original )
).

Definition divide_return_wit_2 := 
(
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (n = 1)) (PreH2 : ((n % ( i ) ) <> 0)) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (n = 1)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors_2)) = cnt)) (PreH13 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  EX (factors: (@list Z)) ,
  “ (PrimeFactorization original factors ) ” 
  &&  “ ((Zlength (factors)) < original) ”
  &&  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + (Zlength (factors)) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (Zlength (factors)) ) original )
) \/
(
forall (p_pre: Z) (original: Z) (factors_2: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : (n = 1)) (PreH2 : ((n % ( i ) ) <> 0)) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (n = 1)) (PreH10 : (0 <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors_2)) = cnt)) (PreH13 : (FactorizationProgress original factors_2 n i )) ,
  (IntArray.seg p_pre 1 (1 + cnt ) factors_2 )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  EX (factors: (@list Z)) ,
  “ (PrimeFactorization original factors ) ” 
  &&  “ ((Zlength (factors)) < original) ”
  &&  (IntArray.seg p_pre 1 (1 + (Zlength (factors)) ) factors )
  **  (IntArray.undef_seg p_pre (1 + (Zlength (factors)) ) original )
).

Definition divide_partial_solve_wit_1 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i )) ,
  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ ((cnt + 1 ) < original) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n >= INT_MIN) ” 
  &&  “ ((n % ( i ) ) = 0) ” 
  &&  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (n = 1) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt < original) ” 
  &&  “ ((Zlength (factors)) = cnt) ” 
  &&  “ (FactorizationProgress original factors n i ) ”
  &&  (((p_pre + ((cnt + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i p_pre (cnt + 1 ) (1 + cnt ) original )
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
.

Definition divide_partial_solve_wit_2 := 
forall (p_pre: Z) (original: Z) (factors: (@list Z)) (cnt: Z) (i: Z) (n: Z) (PreH1 : ((cnt + 1 ) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((n % ( i ) ) = 0)) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i )) ,
  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
  **  (IntArray.undef_seg p_pre (1 + cnt ) original )
|--
  “ ((cnt + 1 ) < original) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n >= INT_MIN) ” 
  &&  “ ((n % ( i ) ) = 0) ” 
  &&  “ (1 <= original) ” 
  &&  “ (original <= INT_MAX) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= original) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= original) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt < original) ” 
  &&  “ ((Zlength (factors)) = cnt) ” 
  &&  “ (FactorizationProgress original factors n i ) ”
  &&  (((p_pre + ((cnt + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i p_pre (cnt + 1 ) (1 + cnt ) original )
  **  (IntArray.undef_seg p_pre 0 1 )
  **  (IntArray.seg p_pre 1 (1 + cnt ) factors )
.

Module Type VC_Correct.


Axiom proof_of_divide_safety_wit_1 : divide_safety_wit_1.
Axiom proof_of_divide_safety_wit_2 : divide_safety_wit_2.
Axiom proof_of_divide_safety_wit_3 : divide_safety_wit_3.
Axiom proof_of_divide_safety_wit_4 : divide_safety_wit_4.
Axiom proof_of_divide_safety_wit_5 : divide_safety_wit_5.
Axiom proof_of_divide_safety_wit_6 : divide_safety_wit_6.
Axiom proof_of_divide_safety_wit_7 : divide_safety_wit_7.
Axiom proof_of_divide_safety_wit_8 : divide_safety_wit_8.
Axiom proof_of_divide_safety_wit_9 : divide_safety_wit_9.
Axiom proof_of_divide_safety_wit_10 : divide_safety_wit_10.
Axiom proof_of_divide_safety_wit_11 : divide_safety_wit_11.
Axiom proof_of_divide_safety_wit_12 : divide_safety_wit_12.
Axiom proof_of_divide_safety_wit_13 : divide_safety_wit_13.
Axiom proof_of_divide_safety_wit_14 : divide_safety_wit_14.
Axiom proof_of_divide_safety_wit_15 : divide_safety_wit_15.
Axiom proof_of_divide_entail_wit_1 : divide_entail_wit_1.
Axiom proof_of_divide_entail_wit_2 : divide_entail_wit_2.
Axiom proof_of_divide_entail_wit_3_1 : divide_entail_wit_3_1.
Axiom proof_of_divide_entail_wit_3_2 : divide_entail_wit_3_2.
Axiom proof_of_divide_entail_wit_4_1 : divide_entail_wit_4_1.
Axiom proof_of_divide_entail_wit_4_2 : divide_entail_wit_4_2.
Axiom proof_of_divide_entail_wit_5 : divide_entail_wit_5.
Axiom proof_of_divide_entail_wit_6 : divide_entail_wit_6.
Axiom proof_of_divide_return_wit_1 : divide_return_wit_1.
Axiom proof_of_divide_return_wit_2 : divide_return_wit_2.
Axiom proof_of_divide_partial_solve_wit_1 : divide_partial_solve_wit_1.
Axiom proof_of_divide_partial_solve_wit_2 : divide_partial_solve_wit_2.

End VC_Correct.
