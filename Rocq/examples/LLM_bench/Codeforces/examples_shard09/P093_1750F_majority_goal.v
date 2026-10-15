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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P093_1750F_majority_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "A" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((n_pre + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 2 )) ”
.

Definition solver_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "A" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Q" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (((2 * n_pre ) + 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * n_pre ) + 4 )) ”
.

Definition solver_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Q" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Q" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Q" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "pow2" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((n_pre + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 2 )) ”
.

Definition solver_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "pow2" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Brow" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((n_pre + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 2 )) ”
.

Definition solver_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Brow" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "P" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_4 (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> retval_4)
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ ((n_pre + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 2 )) ”
.

Definition solver_safety_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "P" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_4 (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> retval_4)
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.undef_full retval_5 (n_pre + 2 ) )
  **  ((( &( "P" ) )) # Ptr  |-> retval_5)
  **  (Int64Array.undef_full retval_4 (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> retval_4)
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre + 2 ))) (PreH7 : ((Zlength (lA)) = i)) (PreH8 : ((Zlength (lBrow)) = i)) (PreH9 : ((Zlength (lP)) = i)) (PreH10 : (lA = (Zeros (i)))) (PreH11 : (lBrow = (Zeros (i)))) (PreH12 : (lP = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A i lA )
  **  (Int64Array.undef_seg A i (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ ((n_pre + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 2 )) ”
.

Definition solver_safety_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre + 2 ))) (PreH7 : ((Zlength (lA)) = i)) (PreH8 : ((Zlength (lBrow)) = i)) (PreH9 : ((Zlength (lP)) = i)) (PreH10 : (lA = (Zeros (i)))) (PreH11 : (lBrow = (Zeros (i)))) (PreH12 : (lP = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A i lA )
  **  (Int64Array.undef_seg A i (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A i lA )
  **  (Int64Array.undef_seg A i (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  (Int64Array.full A (i + 1 ) (app (lA) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  (Int64Array.full Brow (i + 1 ) (app (lBrow) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg Brow (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A (i + 1 ) (app (lA) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  (Int64Array.full P (i + 1 ) (app (lP) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg P (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (i + 1 ) (app (lBrow) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg Brow (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A (i + 1 ) (app (lA) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A i lA )
  **  (Int64Array.undef_seg A i (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (0 <= i)) (PreH6 : (i <= ((2 * n_pre ) + 4 ))) (PreH7 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH8 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH10 : (lA = (Zeros ((n_pre + 2 ))))) (PreH11 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH12 : (lP = (Zeros ((n_pre + 2 ))))) (PreH13 : ((Zlength (lQ)) = i)) (PreH14 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (((2 * n_pre ) + 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * n_pre ) + 4 )) ”
.

Definition solver_safety_wit_22 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (0 <= i)) (PreH6 : (i <= ((2 * n_pre ) + 4 ))) (PreH7 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH8 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH10 : (lA = (Zeros ((n_pre + 2 ))))) (PreH11 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH12 : (lP = (Zeros ((n_pre + 2 ))))) (PreH13 : ((Zlength (lQ)) = i)) (PreH14 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_23 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (0 <= i)) (PreH6 : (i <= ((2 * n_pre ) + 4 ))) (PreH7 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH8 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH10 : (lA = (Zeros ((n_pre + 2 ))))) (PreH11 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH12 : (lP = (Zeros ((n_pre + 2 ))))) (PreH13 : ((Zlength (lQ)) = i)) (PreH14 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_24 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (0 <= i)) (PreH6 : (i <= ((2 * n_pre ) + 4 ))) (PreH7 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH8 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH10 : (lA = (Zeros ((n_pre + 2 ))))) (PreH11 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH12 : (lP = (Zeros ((n_pre + 2 ))))) (PreH13 : ((Zlength (lQ)) = i)) (PreH14 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_25 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  (Int64Array.full Q (i + 1 ) (app (lQ) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg Q (i + 1 ) ((2 * n_pre ) + 4 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_26 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_27 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i >= ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i >= ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ ((1 <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_29 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i >= ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i >= ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  (((pow2 + (0 * sizeof(INT64)))) # Int64  |-> (1 % ( m_pre ) ))
  **  (Int64Array.undef_seg pow2 1 (n_pre + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q i lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_31 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 (i + 1 ) (app (lpow2) ((cons ((((Znth (i - 1 ) lpow2 0) * 2 ) % ( m_pre ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg pow2 (i + 1 ) (n_pre + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ ((((Znth (i - 1 ) lpow2 0) * 2 ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_33 := 
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (((Znth (i - 1 ) lpow2 0) * 2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 1 ) lpow2 0) * 2 )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (((Znth (i - 1 ) lpow2 0) * 2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 1 ) lpow2 0) * 2 )) ”
).

Definition solver_safety_wit_33_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (((Znth (i - 1 ) lpow2 0) * 2 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_33_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ ((INT64_MIN) <= ((Znth (i - 1 ) lpow2 0) * 2 )) ”
.

Definition solver_safety_wit_34 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 i lpow2 )
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_35 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 i lpow2 )
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_37 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 i lpow2 )
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_38 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH14 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  ((( &( "blocked" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_39 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH14 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "blocked" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_40 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i - j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - j )) ”
.

Definition solver_safety_wit_41 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "w" ) )) # Int64  |->_)
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((1 <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_42 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "w" ) )) # Int64  |->_)
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_43 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "z0" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((i - j ) + j ) + 2 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_44 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "z0" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) + j ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - j ) + j ) + 2 )) ”
.

Definition solver_safety_wit_45 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "z0" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((i - j ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - j ) + j )) ”
.

Definition solver_safety_wit_46 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "z0" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_47 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "z0" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_48 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "Lmax" ) )) # Int  |->_)
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "Lmax" ) )) # Int  |->_)
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ”
).

Definition solver_safety_wit_48_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "Lmax" ) )) # Int  |->_)
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition solver_safety_wit_48_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "Lmax" ) )) # Int  |->_)
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT_MIN) <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ”
.

Definition solver_safety_wit_49 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_50 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_51 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre )) ”
).

Definition solver_safety_wit_51_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) <= INT64_MAX) ”
.

Definition solver_safety_wit_51_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre )) ”
.

Definition solver_safety_wit_52 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) )) ”
).

Definition solver_safety_wit_52_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_52_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= (((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) )) ”
.

Definition solver_safety_wit_53 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((1 <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_54 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) )) ”
).

Definition solver_safety_wit_54_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_54_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) )) ”
.

Definition solver_safety_wit_55 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_56 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |->_)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - j ) - j ) - 1 )) ”
.

Definition solver_safety_wit_57 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |->_)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((i - j ) - j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - j ) - j )) ”
.

Definition solver_safety_wit_58 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |->_)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_59 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH2 : (j < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH14 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH16 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH19 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH22 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |->_)
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - j ) - j ) - 1 )) ”
.

Definition solver_safety_wit_60 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH2 : (j < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH14 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH16 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH19 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH22 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |->_)
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((i - j ) - j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - j ) - j )) ”
.

Definition solver_safety_wit_61 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH2 : (j < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH14 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH16 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH19 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH22 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |->_)
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_62 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_63 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH2 : (j < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH14 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH16 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH19 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH22 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_64 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_65 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) )) ”
).

Definition solver_safety_wit_65_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_65_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) )) ”
.

Definition solver_safety_wit_66 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_67 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) )) ”
).

Definition solver_safety_wit_67_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_67_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) )) ”
.

Definition solver_safety_wit_68 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_69 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) )) ”
).

Definition solver_safety_wit_69_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_69_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) )) ”
.

Definition solver_safety_wit_70 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_71 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) )) ”
).

Definition solver_safety_wit_71_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_71_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) )) ”
.

Definition solver_safety_wit_72 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_73 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) )) ”
).

Definition solver_safety_wit_73_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_73_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) )) ”
.

Definition solver_safety_wit_74 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((Znth j lA 0) * (1 % ( m_pre ) ) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_75 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (1 % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (1 % ( m_pre ) ) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (1 % ( m_pre ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth j lA 0) * (1 % ( m_pre ) ) )) ”
).

Definition solver_safety_wit_75_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth j lA 0) * (1 % ( m_pre ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_75_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((Znth j lA 0) * (1 % ( m_pre ) ) )) ”
.

Definition solver_safety_wit_76 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_77 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
).

Definition solver_safety_wit_77_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_77_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
.

Definition solver_safety_wit_78 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_79 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
).

Definition solver_safety_wit_79_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_79_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
.

Definition solver_safety_wit_80 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_81 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
).

Definition solver_safety_wit_81_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_81_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
.

Definition solver_safety_wit_82 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_83 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
).

Definition solver_safety_wit_83_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_83_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= (blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) )) ”
.

Definition solver_safety_wit_84 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) % ( m_pre ) ))
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_85 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) % ( m_pre ) ))
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_86 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) % ( m_pre ) ))
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_87 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0) ) % ( m_pre ) ))
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_88 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((((Znth (i - 1 ) lpow2 0) - blocked ) % ( m_pre ) ) + m_pre ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_89 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((Znth (i - 1 ) lpow2 0) - blocked ) % ( m_pre ) ) + m_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth (i - 1 ) lpow2 0) - blocked ) % ( m_pre ) ) + m_pre )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((Znth (i - 1 ) lpow2 0) - blocked ) % ( m_pre ) ) + m_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth (i - 1 ) lpow2 0) - blocked ) % ( m_pre ) ) + m_pre )) ”
).

Definition solver_safety_wit_89_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((((Znth (i - 1 ) lpow2 0) - blocked ) % ( m_pre ) ) + m_pre ) <= INT64_MAX) ”
.

Definition solver_safety_wit_89_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((((Znth (i - 1 ) lpow2 0) - blocked ) % ( m_pre ) ) + m_pre )) ”
.

Definition solver_safety_wit_90 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((Znth (i - 1 ) lpow2 0) - blocked ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_91 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth (i - 1 ) lpow2 0) - blocked ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 1 ) lpow2 0) - blocked )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth (i - 1 ) lpow2 0) - blocked ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i - 1 ) lpow2 0) - blocked )) ”
).

Definition solver_safety_wit_91_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((Znth (i - 1 ) lpow2 0) - blocked ) <= INT64_MAX) ”
.

Definition solver_safety_wit_91_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= ((Znth (i - 1 ) lpow2 0) - blocked )) ”
.

Definition solver_safety_wit_92 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_93 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_94 := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lpow2: (@list Z)) (lQ: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (i: Z) (blocked: Z) (A: Z) (pow2: Z) (Q: Z) (Brow: Z) (P: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH15 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "run" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_95 := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lpow2: (@list Z)) (lQ: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (i: Z) (blocked: Z) (A: Z) (pow2: Z) (Q: Z) (Brow: Z) (P: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH15 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "run" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_96 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q <= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "c" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_97 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "c" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_98 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "c" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((run + 0 ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_99 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "c" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((run + 0 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (run + 0 )) ”
.

Definition solver_safety_wit_100 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "c" ) )) # Int64  |-> (Znth q lBrow 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((run + (Znth q lBrow 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_101 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "c" ) )) # Int64  |-> (Znth q lBrow 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((run + (Znth q lBrow 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (run + (Znth q lBrow 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "c" ) )) # Int64  |-> (Znth q lBrow 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((run + (Znth q lBrow 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (run + (Znth q lBrow 0) )) ”
).

Definition solver_safety_wit_101_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "c" ) )) # Int64  |-> (Znth q lBrow 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((run + (Znth q lBrow 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_101_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "c" ) )) # Int64  |-> (Znth q lBrow 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= (run + (Znth q lBrow 0) )) ”
.

Definition solver_safety_wit_102 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "c" ) )) # Int64  |-> (Znth i lA 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (((run + (Znth i lA 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_103 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "c" ) )) # Int64  |-> (Znth i lA 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((run + (Znth i lA 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (run + (Znth i lA 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "c" ) )) # Int64  |-> (Znth i lA 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((run + (Znth i lA 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (run + (Znth i lA 0) )) ”
).

Definition solver_safety_wit_103_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "c" ) )) # Int64  |-> (Znth i lA 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((run + (Znth i lA 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_103_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "c" ) )) # Int64  |-> (Znth i lA 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((INT64_MIN) <= (run + (Znth i lA 0) )) ”
.

Definition solver_safety_wit_104 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) (replace_Znth (q) (((run + 0 ) % ( m_pre ) )) (lP)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> ((run + 0 ) % ( m_pre ) ))
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ ((q + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_105 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) (replace_Znth (q) (((run + (Znth q lBrow 0) ) % ( m_pre ) )) (lP)) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> ((run + (Znth q lBrow 0) ) % ( m_pre ) ))
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ ((q + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_106 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) (replace_Znth (q) (((run + (Znth i lA 0) ) % ( m_pre ) )) (lP)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> ((run + (Znth i lA 0) ) % ( m_pre ) ))
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ ((q + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (q + 1 )) ”
.

Definition solver_safety_wit_107 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_108 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition solver_safety_wit_109 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i + t ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + t )) ”
.

Definition solver_safety_wit_110 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t < i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_111 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) > (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ False ”
.

Definition solver_safety_wit_112 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i + t ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + t )) ”
.

Definition solver_safety_wit_113 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ ((((Znth (i + t ) lQ 0) + (Znth t lP 0) ) <> (INT64_MIN)) \/ (m_pre <> (-1))) ” 
  &&  “ (m_pre <> 0) ”
.

Definition solver_safety_wit_114 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ (((Znth (i + t ) lQ 0) + (Znth t lP 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i + t ) lQ 0) + (Znth t lP 0) )) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ (((Znth (i + t ) lQ 0) + (Znth t lP 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (i + t ) lQ 0) + (Znth t lP 0) )) ”
).

Definition solver_safety_wit_114_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ (((Znth (i + t ) lQ 0) + (Znth t lP 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_114_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ ((INT64_MIN) <= ((Znth (i + t ) lQ 0) + (Znth t lP 0) )) ”
.

Definition solver_safety_wit_115 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i + t ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + t )) ”
.

Definition solver_safety_wit_116 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) (replace_Znth ((i + t )) ((((Znth (i + t ) lQ 0) + (Znth t lP 0) ) % ( m_pre ) )) (lQ)) )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "run" ) )) # Int64  |-> run)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition solver_safety_wit_117 := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lpow2: (@list Z)) (lQ: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (i: Z) (blocked: Z) (run: Z) (A: Z) (pow2: Z) (Q: Z) (Brow: Z) (P: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH17 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ = (DPQ (m_pre) (n_pre) (i)))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  (Int64Array.undef_full retval_5 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_4 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA)) = 0) ” 
  &&  “ ((Zlength (lBrow)) = 0) ” 
  &&  “ ((Zlength (lP)) = 0) ” 
  &&  “ (lA = (Zeros (0))) ” 
  &&  “ (lBrow = (Zeros (0))) ” 
  &&  “ (lP = (Zeros (0))) ”
  &&  (Int64Array.full retval 0 lA )
  **  (Int64Array.undef_seg retval 0 (n_pre + 2 ) )
  **  (Int64Array.full retval_4 0 lBrow )
  **  (Int64Array.undef_seg retval_4 0 (n_pre + 2 ) )
  **  (Int64Array.full retval_5 0 lP )
  **  (Int64Array.undef_seg retval_5 0 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  TT && emp 
|--
  “ ((Zlength ((Zeros (0)))) = 0) ” 
  &&  “ ((Zlength ((Zeros (0)))) = 0) ” 
  &&  “ ((Zlength ((Zeros (0)))) = 0) ” 
  &&  “ ((Zeros (0)) = (@nil Z)) ” 
  &&  “ ((Zeros (0)) = (@nil Z)) ” 
  &&  “ ((Zeros (0)) = (@nil Z)) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((Zlength ((Zeros (0)))) = 0)
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((Zlength ((Zeros (0)))) = 0)
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((Zlength ((Zeros (0)))) = 0)
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((Zeros (0)) = (@nil Z))
.

Definition solver_entail_wit_1_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((Zeros (0)) = (@nil Z))
.

Definition solver_entail_wit_1_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((Zeros (0)) = (@nil Z))
.

Definition solver_entail_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full P (i + 1 ) (app (lP_2) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg P (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (i + 1 ) (app (lBrow_2) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg Brow (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A (i + 1 ) (app (lA_2) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA)) = (i + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (i + 1 )) ” 
  &&  “ ((Zlength (lP)) = (i + 1 )) ” 
  &&  “ (lA = (Zeros ((i + 1 )))) ” 
  &&  “ (lBrow = (Zeros ((i + 1 )))) ” 
  &&  “ (lP = (Zeros ((i + 1 )))) ”
  &&  (Int64Array.full A (i + 1 ) lA )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (i + 1 ) lBrow )
  **  (Int64Array.undef_seg Brow (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (i + 1 ) lP )
  **  (Int64Array.undef_seg P (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  TT && emp 
|--
  “ ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 )) ” 
  &&  “ ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 )) ” 
  &&  “ ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 )) ” 
  &&  “ ((app (lP_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 )))) ” 
  &&  “ ((app (lBrow_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 )))) ” 
  &&  “ ((app (lA_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 ))
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 ))
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 ))
.

Definition solver_entail_wit_2_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  ((app (lP_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 ))))
.

Definition solver_entail_wit_2_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  ((app (lBrow_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 ))))
.

Definition solver_entail_wit_2_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  ((app (lA_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 ))))
.

Definition solver_entail_wit_3 := 
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.undef_seg A i (n_pre + 2 ) )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  (Int64Array.full P i lP_2 )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  EX (lQ: (@list Z))  (lP: (@list Z))  (lBrow: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = 0) ” 
  &&  “ (lQ = (Zeros (0))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q 0 lQ )
  **  (Int64Array.undef_seg Q 0 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.full P i lP_2 )
|--
  “ ((Zlength ((Zeros (0)))) = 0) ” 
  &&  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ” 
  &&  “ ((Zeros (0)) = (@nil Z)) ”
  &&  (Int64Array.full A (n_pre + 2 ) (Zeros ((n_pre + 2 ))) )
  **  (Int64Array.full Brow (n_pre + 2 ) (Zeros ((n_pre + 2 ))) )
  **  (Int64Array.full P (n_pre + 2 ) (Zeros ((n_pre + 2 ))) )
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.full P i lP_2 )
|--
  “ ((Zlength ((Zeros (0)))) = 0) ”
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.full P i lP_2 )
|--
  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ”
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.full P i lP_2 )
|--
  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ”
.

Definition solver_entail_wit_3_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.full P i lP_2 )
|--
  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ”
.

Definition solver_entail_wit_3_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.full P i lP_2 )
|--
  “ ((Zeros (0)) = (@nil Z)) ”
.

Definition solver_entail_wit_3_split_goal_spatial := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA_2)) = i)) (PreH9 : ((Zlength (lBrow_2)) = i)) (PreH10 : ((Zlength (lP_2)) = i)) (PreH11 : (lA_2 = (Zeros (i)))) (PreH12 : (lBrow_2 = (Zeros (i)))) (PreH13 : (lP_2 = (Zeros (i)))) ,
  (Int64Array.full A i lA_2 )
  **  (Int64Array.full Brow i lBrow_2 )
  **  (Int64Array.full P i lP_2 )
|--
  (Int64Array.full A (n_pre + 2 ) (Zeros ((n_pre + 2 ))) )
  **  (Int64Array.full Brow (n_pre + 2 ) (Zeros ((n_pre + 2 ))) )
  **  (Int64Array.full P (n_pre + 2 ) (Zeros ((n_pre + 2 ))) )
.

Definition solver_entail_wit_4 := 
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  (Int64Array.full Q (i + 1 ) (app (lQ_2) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg Q (i + 1 ) ((2 * n_pre ) + 4 ) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  EX (lQ: (@list Z))  (lP: (@list Z))  (lBrow: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = (i + 1 )) ” 
  &&  “ (lQ = (Zeros ((i + 1 )))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q (i + 1 ) lQ )
  **  (Int64Array.undef_seg Q (i + 1 ) ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  TT && emp 
|--
  “ ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ ((app (lQ_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  ((Zlength ((Zeros ((i + 1 ))))) = (i + 1 ))
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_4_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  ((app (lQ_2) ((cons (0) ((@nil Z))))) = (Zeros ((i + 1 ))))
.

Definition solver_entail_wit_5 := 
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i >= ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = i)) (PreH15 : (lQ_2 = (Zeros (i)))) ,
  (((pow2 + (0 * sizeof(INT64)))) # Int64  |-> (1 % ( m_pre ) ))
  **  (Int64Array.undef_seg pow2 1 (n_pre + 2 ) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
  **  (Int64Array.full Q i lQ_2 )
|--
  EX (lpow2: (@list Z))  (lQ: (@list Z))  (lP: (@list Z))  (lBrow: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ (lQ = (Zeros (((2 * n_pre ) + 4 )))) ” 
  &&  “ ((Zlength (lpow2)) = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 1)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 1 lpow2 )
  **  (Int64Array.undef_seg pow2 1 (n_pre + 2 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH2 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH3 : (i >= ((2 * n_pre ) + 4 ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= ((2 * n_pre ) + 4 ))) (PreH10 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH15 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH16 : ((Zlength (lQ_2)) = i)) (PreH17 : (lQ_2 = (Zeros (i)))) ,
  (((pow2 + (0 * sizeof(INT64)))) # Int64  |-> (1 % ( m_pre ) ))
  **  (Int64Array.full Q i lQ_2 )
|--
  EX (lpow2: (@list Z)) ,
  “ (lP_2 = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow_2 = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lA_2 = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((Zeros ((n_pre + 2 ))))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((Zeros (((2 * n_pre ) + 4 ))))) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 1)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ”
  &&  (Int64Array.full Q ((2 * n_pre ) + 4 ) (Zeros (((2 * n_pre ) + 4 ))) )
  **  (Int64Array.full pow2 1 lpow2 )
).

Definition solver_entail_wit_6 := 
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 (i + 1 ) (app (lpow2_2) ((cons ((((Znth (i - 1 ) lpow2_2 0) * 2 ) % ( m_pre ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg pow2 (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
|--
  EX (lpow2: (@list Z))  (lQ: (@list Z))  (lP: (@list Z))  (lBrow: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ (lQ = (Zeros (((2 * n_pre ) + 4 )))) ” 
  &&  “ ((Zlength (lpow2)) = (i + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (i + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (i + 1 ) (n_pre + 2 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  TT && emp 
|--
  “ ((Zlength ((app (lpow2_2) ((cons ((((Znth (i - 1 ) lpow2_2 0) * 2 ) % ( m_pre ) )) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((Zlength ((app (lpow2_2) ((cons ((((Znth (i - 1 ) lpow2_2 0) * 2 ) % ( m_pre ) )) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_6_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_6_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_6_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_6_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_7 := 
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) ,
  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full pow2 i lpow2_2 )
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((1 - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((1 - 1 )))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH11 : (lA_2 = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow_2 = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP_2 = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ_2 = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2_2)) = i)) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2_2 )
|--
  EX (lpow2: (@list Z)) ,
  “ (lQ_2 = (DPQ (m_pre) (n_pre) ((1 - 1 )))) ” 
  &&  “ (lA_2 = (DPA (m_pre) (n_pre) ((1 - 1 )))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength ((DPA (m_pre) (n_pre) ((1 - 1 ))))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength ((DPQ (m_pre) (n_pre) ((1 - 1 ))))) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow_2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP_2)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ”
  &&  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
).

Definition solver_entail_wit_8 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH14 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= i) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (0 = (RowBlocked (m_pre) (n_pre) (i) ((1 - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < 1)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH14 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  TT && emp 
|--
  “ forall (jj: Z) , (((1 <= jj) /\ (jj < 1)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ (0 = (RowBlocked (m_pre) (n_pre) (i) ((1 - 1 )))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH14 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  forall (jj: Z) , (((1 <= jj) /\ (jj < 1)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH14 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  (0 = (RowBlocked (m_pre) (n_pre) (i) ((1 - 1 ))))
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH14 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))
.

Definition solver_entail_wit_8_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH14 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_8_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH14 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_9 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH2 : (j < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH14 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH15 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH16 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH19 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH22 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (blocked <= INT64_MAX)) (PreH2 : (m_pre <= INT64_MAX)) (PreH3 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH4 : (blocked >= INT64_MIN)) (PreH5 : (m_pre >= INT64_MIN)) (PreH6 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH7 : (j <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((i - j ) <= INT_MAX)) (PreH11 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH12 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : ((i - j ) >= INT_MIN)) (PreH17 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH18 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  TT && emp 
|--
  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (blocked <= INT64_MAX)) (PreH2 : (m_pre <= INT64_MAX)) (PreH3 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH4 : (blocked >= INT64_MIN)) (PreH5 : (m_pre >= INT64_MIN)) (PreH6 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH7 : (j <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((i - j ) <= INT_MAX)) (PreH11 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH12 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH13 : (j >= INT_MIN)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : ((i - j ) >= INT_MIN)) (PreH17 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH18 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))
.

Definition solver_entail_wit_10_1 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_entail_wit_10_2 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  ((( &( "D" ) )) # Int  |-> (((i - j ) - j ) - 1 ))
  **  ((( &( "Lmax" ) )) # Int  |-> ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))
  **  ((( &( "z0" ) )) # Int  |-> ((((i - j ) + j ) + 2 ) ÷ 2 ))
  **  ((( &( "w" ) )) # Int64  |-> (1 % ( m_pre ) ))
  **  ((( &( "d" ) )) # Int  |-> (i - j ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "blocked" ) )) # Int64  |-> blocked)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_entail_wit_11_1 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < (j + 1 ))) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  TT && emp 
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 ))))
.

Definition solver_entail_wit_11_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_11_1_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_1_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_11_1_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ))
.

Definition solver_entail_wit_11_2 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < (j + 1 ))) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  TT && emp 
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 ))))
.

Definition solver_entail_wit_11_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_2_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_11_2_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_2_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_11_2_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ_2 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ))
.

Definition solver_entail_wit_11_3 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < (j + 1 ))) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  TT && emp 
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 ))))
.

Definition solver_entail_wit_11_3_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_3_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_11_3_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_3_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_11_3_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2_2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ))
.

Definition solver_entail_wit_11_4 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < (j + 1 ))) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  TT && emp 
|--
  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_11_4_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) = (RowBlocked (m_pre) (n_pre) (i) (((j + 1 ) - 1 ))))
.

Definition solver_entail_wit_11_4_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength ((replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_4_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_11_4_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_11_4_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_11_4_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (0 <= ((blocked + (Znth j (replace_Znth (j) ((((Znth j lA_2 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow_2)) 0) ) % ( m_pre ) ))
.

Definition solver_entail_wit_12 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  (Int64Array.full A (n_pre + 2 ) (replace_Znth (i) ((((((Znth (i - 1 ) lpow2_2 0) - blocked ) % ( m_pre ) ) + m_pre ) % ( m_pre ) )) (lA_2)) )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  TT && emp 
|--
  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength ((DPA (m_pre) (n_pre) (i)))) = (n_pre + 2 )) ” 
  &&  “ ((replace_Znth (i) ((((((Znth (i - 1 ) lpow2_2 0) - blocked ) % ( m_pre ) ) + m_pre ) % ( m_pre ) )) (lA_2)) = (DPA (m_pre) (n_pre) (i))) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))
.

Definition solver_entail_wit_12_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))
.

Definition solver_entail_wit_12_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))
.

Definition solver_entail_wit_12_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_12_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  ((Zlength ((DPA (m_pre) (n_pre) (i)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_12_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH18 : (lA_2 = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < j)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  ((replace_Znth (i) ((((((Znth (i - 1 ) lpow2_2 0) - blocked ) % ( m_pre ) ) + m_pre ) % ( m_pre ) )) (lA_2)) = (DPA (m_pre) (n_pre) (i)))
.

Definition solver_entail_wit_13 := 
(
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (A: Z) (pow2: Z) (Q: Z) (Brow: Z) (P: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (0 = (RowRun (m_pre) (n_pre) (i) (0))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < 0)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  TT && emp 
|--
  “ forall (qq: Z) , (((0 <= qq) /\ (qq < 0)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ (0 = (RowRun (m_pre) (n_pre) (i) (0))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  forall (qq: Z) , (((0 <= qq) /\ (qq < 0)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))
.

Definition solver_entail_wit_13_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))
.

Definition solver_entail_wit_13_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  (0 = (RowRun (m_pre) (n_pre) (i) (0)))
.

Definition solver_entail_wit_13_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))
.

Definition solver_entail_wit_13_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_13_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH11 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH12 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH15 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH16 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH17 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH18 : forall (jj_2: Z) , (((1 <= jj_2) /\ (jj_2 < i)) -> ((Znth (jj_2) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj_2))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_14_1 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) (replace_Znth (q) (((run + 0 ) % ( m_pre ) )) (lP_2)) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (q + 1 )) ” 
  &&  “ ((q + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= ((run + 0 ) % ( m_pre ) )) ” 
  &&  “ (((run + 0 ) % ( m_pre ) ) < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (((run + 0 ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((q + 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < (q + 1 ))) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  TT && emp 
|--
  “ (((run + 0 ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((0 + 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth (0) (((run + 0 ) % ( m_pre ) )) (lP_2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (((run + 0 ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((run + 0 ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (((run + 0 ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((0 + 1 ))))
.

Definition solver_entail_wit_14_1_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength ((replace_Znth (0) (((run + 0 ) % ( m_pre ) )) (lP_2)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_14_1_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_14_1_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_14_1_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (((run + 0 ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_14_1_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (0 <= ((run + 0 ) % ( m_pre ) ))
.

Definition solver_entail_wit_14_2 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) (replace_Znth (q) (((run + (Znth q lBrow_2 0) ) % ( m_pre ) )) (lP_2)) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (q + 1 )) ” 
  &&  “ ((q + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= ((run + (Znth q lBrow_2 0) ) % ( m_pre ) )) ” 
  &&  “ (((run + (Znth q lBrow_2 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (((run + (Znth q lBrow_2 0) ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((q + 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < (q + 1 ))) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  TT && emp 
|--
  “ (((run + (Znth q lBrow_2 0) ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((q + 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth (q) (((run + (Znth q lBrow_2 0) ) % ( m_pre ) )) (lP_2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (((run + (Znth q lBrow_2 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((run + (Znth q lBrow_2 0) ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (((run + (Znth q lBrow_2 0) ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((q + 1 ))))
.

Definition solver_entail_wit_14_2_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength ((replace_Znth (q) (((run + (Znth q lBrow_2 0) ) % ( m_pre ) )) (lP_2)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_14_2_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_14_2_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_14_2_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (((run + (Znth q lBrow_2 0) ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_14_2_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (0 <= ((run + (Znth q lBrow_2 0) ) % ( m_pre ) ))
.

Definition solver_entail_wit_14_3 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) (replace_Znth (q) (((run + (Znth i lA_2 0) ) % ( m_pre ) )) (lP_2)) )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (q + 1 )) ” 
  &&  “ ((q + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= ((run + (Znth i lA_2 0) ) % ( m_pre ) )) ” 
  &&  “ (((run + (Znth i lA_2 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (((run + (Znth i lA_2 0) ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((q + 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < (q + 1 ))) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  TT && emp 
|--
  “ (((run + (Znth i lA_2 0) ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((q + 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth (q) (((run + (Znth i lA_2 0) ) % ( m_pre ) )) (lP_2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (((run + (Znth i lA_2 0) ) % ( m_pre ) ) < m_pre) ” 
  &&  “ (0 <= ((run + (Znth i lA_2 0) ) % ( m_pre ) )) ”
  &&  emp
).

Definition solver_entail_wit_14_3_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (((run + (Znth i lA_2 0) ) % ( m_pre ) ) = (RowRun (m_pre) (n_pre) (i) ((q + 1 ))))
.

Definition solver_entail_wit_14_3_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength ((replace_Znth (q) (((run + (Znth i lA_2 0) ) % ( m_pre ) )) (lP_2)))) = (n_pre + 2 ))
.

Definition solver_entail_wit_14_3_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_14_3_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_14_3_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (((run + (Znth i lA_2 0) ) % ( m_pre ) ) < m_pre)
.

Definition solver_entail_wit_14_3_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (0 <= ((run + (Znth i lA_2 0) ) % ( m_pre ) ))
.

Definition solver_entail_wit_15 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (QPartial (m_pre) (n_pre) (i) (0))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 )))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  TT && emp 
|--
  “ forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 )))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ ((Zlength ((QPartial (m_pre) (n_pre) (i) (0)))) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (lQ_2 = (QPartial (m_pre) (n_pre) (i) (0))) ”
  &&  emp
).

Definition solver_entail_wit_15_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))
.

Definition solver_entail_wit_15_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))
.

Definition solver_entail_wit_15_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))
.

Definition solver_entail_wit_15_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  ((Zlength ((QPartial (m_pre) (n_pre) (i) (0)))) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_15_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_15_split_goal_6 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q > i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= q)) (PreH9 : (q <= (i + 1 ))) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH24 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow_2) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH25 : forall (qq_2: Z) , (((0 <= qq_2) /\ (qq_2 < q)) -> ((Znth (qq_2) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq_2))))) ,
  (lQ_2 = (QPartial (m_pre) (n_pre) (i) (0)))
.

Definition solver_entail_wit_16 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) (i))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ ((Zlength ((DPQ (m_pre) (n_pre) (i)))) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ (lQ_2 = (DPQ (m_pre) (n_pre) (i))) ”
  &&  emp
).

Definition solver_entail_wit_16_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))
.

Definition solver_entail_wit_16_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength ((DPQ (m_pre) (n_pre) (i)))) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_16_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_16_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : (t >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= t)) (PreH9 : (t <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : (0 <= run)) (PreH13 : (run < m_pre)) (PreH14 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH20 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH21 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH23 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH24 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (lQ_2 = (DPQ (m_pre) (n_pre) (i)))
.

Definition solver_entail_wit_17 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) (replace_Znth ((i + t )) ((((Znth (i + t ) lQ_2 0) + (Znth t lP_2 0) ) % ( m_pre ) )) (lQ_2)) )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
  **  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (QPartial (m_pre) (n_pre) (i) ((t + 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 )))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  TT && emp 
|--
  “ ((Zlength ((QPartial (m_pre) (n_pre) (i) ((t + 1 ))))) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ ((replace_Znth ((i + t )) ((((Znth (i + t ) lQ_2 0) + (Znth t lP_2 0) ) % ( m_pre ) )) (lQ_2)) = (QPartial (m_pre) (n_pre) (i) ((t + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_17_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength ((QPartial (m_pre) (n_pre) (i) ((t + 1 ))))) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_17_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((Zlength (lA_2)) = (n_pre + 2 ))
.

Definition solver_entail_wit_17_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA_2: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ_2 = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP_2) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  ((replace_Znth ((i + t )) ((((Znth (i + t ) lQ_2 0) + (Znth t lP_2 0) ) % ( m_pre ) )) (lQ_2)) = (QPartial (m_pre) (n_pre) (i) ((t + 1 ))))
.

Definition solver_entail_wit_18 := 
(
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (run: Z) (A: Z) (pow2: Z) (Q: Z) (Brow: Z) (P: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH17 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ_2 = (DPQ (m_pre) (n_pre) (i)))) ,
  (Int64Array.full A (n_pre + 2 ) lA_2 )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lQ: (@list Z))  (lpow2: (@list Z))  (lA: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (((i + 1 ) - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) (((i + 1 ) - 1 )))) ”
  &&  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (run: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH17 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ_2 = (DPQ (m_pre) (n_pre) (i)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ ((Zlength ((DPQ (m_pre) (n_pre) (((i + 1 ) - 1 ))))) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength ((DPA (m_pre) (n_pre) (((i + 1 ) - 1 ))))) = (n_pre + 2 )) ” 
  &&  “ (lA_2 = (DPA (m_pre) (n_pre) (((i + 1 ) - 1 )))) ” 
  &&  “ (lQ_2 = (DPQ (m_pre) (n_pre) (((i + 1 ) - 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_18_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (run: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH17 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ_2 = (DPQ (m_pre) (n_pre) (i)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))
.

Definition solver_entail_wit_18_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (run: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH17 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ_2 = (DPQ (m_pre) (n_pre) (i)))) ,
  ((Zlength ((DPQ (m_pre) (n_pre) (((i + 1 ) - 1 ))))) = ((2 * n_pre ) + 4 ))
.

Definition solver_entail_wit_18_split_goal_3 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (run: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH17 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ_2 = (DPQ (m_pre) (n_pre) (i)))) ,
  ((Zlength ((DPA (m_pre) (n_pre) (((i + 1 ) - 1 ))))) = (n_pre + 2 ))
.

Definition solver_entail_wit_18_split_goal_4 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (run: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH17 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ_2 = (DPQ (m_pre) (n_pre) (i)))) ,
  (lA_2 = (DPA (m_pre) (n_pre) (((i + 1 ) - 1 ))))
.

Definition solver_entail_wit_18_split_goal_5 := 
forall (m_pre: Z) (n_pre: Z) (lA_2: (@list Z)) (lpow2_2: (@list Z)) (lQ_2: (@list Z)) (lBrow_2: (@list Z)) (lP_2: (@list Z)) (i: Z) (blocked: Z) (run: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= blocked)) (PreH8 : (blocked < m_pre)) (PreH9 : (0 <= run)) (PreH10 : (run < m_pre)) (PreH11 : ((Zlength (lA_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH13 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH14 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (n_pre + 1 ))) -> ((Znth (k_2) (lpow2_2) (0)) = (Pow2Mod (k_2) (m_pre))))) (PreH17 : (lA_2 = (DPA (m_pre) (n_pre) (i)))) (PreH18 : (lQ_2 = (DPQ (m_pre) (n_pre) (i)))) ,
  (lQ_2 = (DPQ (m_pre) (n_pre) (((i + 1 ) - 1 ))))
.

Definition solver_entail_wit_19 := 
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH14 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (cP: (@list (@option Z)))  (cBrow: (@list (@option Z)))  (cpow2: (@list (@option Z)))  (cQ: (@list (@option Z)))  (cA: (@list (@option Z)))  (lP: (@list Z))  (lBrow: (@list Z))  (lpow2: (@list Z))  (lQ: (@list Z))  (lA_2: (@list Z)) ,
  “ (i = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((Zlength (lA_2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA_2 = (DPA (m_pre) (n_pre) (n_pre))) ” 
  &&  “ ((Znth n_pre lA 0) = (Znth (n_pre) (lA_2) (0))) ” 
  &&  “ (Spec n_pre m_pre (Znth n_pre lA 0) ) ” 
  &&  “ (cA = (SomeList (lA_2))) ” 
  &&  “ (cQ = (SomeList (lQ))) ” 
  &&  “ (cpow2 = (SomeListUndefTail (lpow2))) ” 
  &&  “ (cBrow = (SomeList (lBrow))) ” 
  &&  “ (cP = (SomeList (lP))) ” 
  &&  “ ((Zlength (cA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (cpow2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cP)) = (n_pre + 2 )) ”
  &&  (Int64Array.mixed_full A (Zlength (cA)) cA )
  **  (Int64Array.mixed_full Q (Zlength (cQ)) cQ )
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
) \/
(
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP_2: (@list Z)) (lBrow_2: (@list Z)) (lQ_2: (@list Z)) (lpow2_2: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2_2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ_2)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow_2)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP_2)) = (n_pre + 2 ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2_2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH14 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ_2 = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2_2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ_2 )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow_2 )
  **  (Int64Array.full P (n_pre + 2 ) lP_2 )
|--
  EX (lP: (@list Z))  (lBrow: (@list Z))  (lpow2: (@list Z))  (lQ: (@list Z)) ,
  “ (i = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((Zlength ((DPA (m_pre) (n_pre) (n_pre)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ ((Znth n_pre lA 0) = (Znth (n_pre) ((DPA (m_pre) (n_pre) (n_pre))) (0))) ” 
  &&  “ (Spec n_pre m_pre (Znth n_pre lA 0) ) ” 
  &&  “ ((Zlength ((SomeList ((DPA (m_pre) (n_pre) (n_pre)))))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((SomeList (lQ)))) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength ((SomeListUndefTail (lpow2)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((SomeList (lBrow)))) = (n_pre + 2 )) ” 
  &&  “ ((Zlength ((SomeList (lP)))) = (n_pre + 2 )) ”
  &&  (Int64Array.mixed_full A (Zlength ((SomeList ((DPA (m_pre) (n_pre) (n_pre)))))) (SomeList ((DPA (m_pre) (n_pre) (n_pre)))) )
  **  (Int64Array.mixed_full Q (Zlength ((SomeList (lQ)))) (SomeList (lQ)) )
  **  (Int64Array.mixed_full pow2 (Zlength ((SomeListUndefTail (lpow2)))) (SomeListUndefTail (lpow2)) )
  **  (Int64Array.mixed_full Brow (Zlength ((SomeList (lBrow)))) (SomeList (lBrow)) )
  **  (Int64Array.mixed_full P (Zlength ((SomeList (lP)))) (SomeList (lP)) )
).

Definition solver_return_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  TT && emp 
|--
  “ (Spec n_pre m_pre ans ) ”
  &&  emp
.

Definition solver_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "A" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ”
  &&  emp
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Q" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (0 <= ((2 * n_pre ) + 4 )) ” 
  &&  “ ((((2 * n_pre ) + 4 ) * sizeof(INT64) ) = (((2 * n_pre ) + 4 ) * 8 )) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  (Int64Array.undef_full retval (n_pre + 2 ) )
|--
  “ (0 <= ((2 * n_pre ) + 4 )) ” 
  &&  “ ((((2 * n_pre ) + 4 ) * sizeof(INT64) ) = (((2 * n_pre ) + 4 ) * 8 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ”
  &&  (Int64Array.undef_full retval (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3_pure := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "pow2" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ”
  &&  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4_pure := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "Brow" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ”
.

Definition solver_partial_solve_wit_4_aux := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ”
  &&  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5_pure := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  ((( &( "P" ) )) # Ptr  |->_)
  **  (Int64Array.undef_full retval_4 (n_pre + 2 ) )
  **  ((( &( "Brow" ) )) # Ptr  |-> retval_4)
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  ((( &( "pow2" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  ((( &( "Q" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
  **  ((( &( "A" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ”
.

Definition solver_partial_solve_wit_5_aux := 
forall (m_pre: Z) (n_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5000)) (PreH3 : (10 <= m_pre)) (PreH4 : (m_pre <= 1000000000)) ,
  (Int64Array.undef_full retval_4 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
|--
  “ (0 <= (n_pre + 2 )) ” 
  &&  “ (((n_pre + 2 ) * sizeof(INT64) ) = ((n_pre + 2 ) * 8 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ”
  &&  (Int64Array.undef_full retval_4 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_3 (n_pre + 2 ) )
  **  (Int64Array.undef_full retval_2 ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full retval (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Definition solver_partial_solve_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  (Int64Array.full A i lA )
  **  (Int64Array.undef_seg A i (n_pre + 2 ) )
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (i < (n_pre + 2 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA)) = i) ” 
  &&  “ ((Zlength (lBrow)) = i) ” 
  &&  “ ((Zlength (lP)) = i) ” 
  &&  “ (lA = (Zeros (i))) ” 
  &&  “ (lBrow = (Zeros (i))) ” 
  &&  “ (lP = (Zeros (i))) ”
  &&  (((A + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A i lA )
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  (Int64Array.full A (i + 1 ) (app (lA) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.undef_seg Brow i (n_pre + 2 ) )
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (i < (n_pre + 2 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA)) = i) ” 
  &&  “ ((Zlength (lBrow)) = i) ” 
  &&  “ ((Zlength (lP)) = i) ” 
  &&  “ (lA = (Zeros (i))) ” 
  &&  “ (lBrow = (Zeros (i))) ” 
  &&  “ (lP = (Zeros (i))) ”
  &&  (((Brow + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg Brow (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A (i + 1 ) (app (lA) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow i lBrow )
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < (n_pre + 2 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre + 2 ))) (PreH8 : ((Zlength (lA)) = i)) (PreH9 : ((Zlength (lBrow)) = i)) (PreH10 : ((Zlength (lP)) = i)) (PreH11 : (lA = (Zeros (i)))) (PreH12 : (lBrow = (Zeros (i)))) (PreH13 : (lP = (Zeros (i)))) ,
  (Int64Array.full Brow (i + 1 ) (app (lBrow) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg Brow (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A (i + 1 ) (app (lA) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_seg P i (n_pre + 2 ) )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (i < (n_pre + 2 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre + 2 )) ” 
  &&  “ ((Zlength (lA)) = i) ” 
  &&  “ ((Zlength (lBrow)) = i) ” 
  &&  “ ((Zlength (lP)) = i) ” 
  &&  “ (lA = (Zeros (i))) ” 
  &&  “ (lBrow = (Zeros (i))) ” 
  &&  “ (lP = (Zeros (i))) ”
  &&  (((P + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg P (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (i + 1 ) (app (lBrow) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg Brow (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full A (i + 1 ) (app (lA) ((cons (0) ((@nil Z))))) )
  **  (Int64Array.undef_seg A (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P i lP )
  **  (Int64Array.undef_full Q ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i < ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (i < ((2 * n_pre ) + 4 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = i) ” 
  &&  “ (lQ = (Zeros (i))) ”
  &&  (((Q + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg Q (i + 1 ) ((2 * n_pre ) + 4 ) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i >= ((2 * n_pre ) + 4 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (0 <= i)) (PreH7 : (i <= ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = i)) (PreH15 : (lQ = (Zeros (i)))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q i lQ )
  **  (Int64Array.undef_seg Q i ((2 * n_pre ) + 4 ) )
  **  (Int64Array.undef_full pow2 (n_pre + 2 ) )
|--
  “ (i >= ((2 * n_pre ) + 4 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = i) ” 
  &&  “ (lQ = (Zeros (i))) ”
  &&  (((pow2 + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg pow2 1 (n_pre + 2 ) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q i lQ )
.

Definition solver_partial_solve_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 i lpow2 )
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ (lQ = (Zeros (((2 * n_pre ) + 4 )))) ” 
  &&  “ ((Zlength (lpow2)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ”
  &&  (((pow2 + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i - 1 ) lpow2 0))
  **  (Int64Array.missing_i pow2 (i - 1 ) 0 i lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
.

Definition solver_partial_solve_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (pow2: Z) (Q: Z) (P: Z) (Brow: Z) (A: Z) (lpow2: (@list Z)) (lQ: (@list Z)) (lP: (@list Z)) (lBrow: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (Zeros ((n_pre + 2 ))))) (PreH12 : (lBrow = (Zeros ((n_pre + 2 ))))) (PreH13 : (lP = (Zeros ((n_pre + 2 ))))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : (lQ = (Zeros (((2 * n_pre ) + 4 ))))) (PreH16 : ((Zlength (lpow2)) = i)) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) ,
  (Int64Array.full pow2 i lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.undef_seg pow2 i (n_pre + 2 ) )
|--
  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lBrow = (Zeros ((n_pre + 2 )))) ” 
  &&  “ (lP = (Zeros ((n_pre + 2 )))) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ (lQ = (Zeros (((2 * n_pre ) + 4 )))) ” 
  &&  “ ((Zlength (lpow2)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ”
  &&  (((pow2 + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg pow2 (i + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full pow2 i lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
.

Definition solver_partial_solve_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (n_pre >= INT_MIN)) (PreH17 : ((i - j ) >= INT_MIN)) (PreH18 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH19 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH20 : (j < i)) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 5000)) (PreH23 : (10 <= m_pre)) (PreH24 : (m_pre <= 1000000000)) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= i)) (PreH29 : (0 <= blocked)) (PreH30 : (blocked < m_pre)) (PreH31 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH32 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH33 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH34 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH36 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH37 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH38 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH40 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((pow2 + (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0))
  **  (Int64Array.missing_i pow2 ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) 0 (n_pre + 1 ) lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_14 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Q + ((((i - j ) - j ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - j ) - j ) - 1 ) lQ 0))
  **  (Int64Array.missing_i Q (((i - j ) - j ) - 1 ) 0 ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Q + ((((i - j ) - j ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((i - j ) - j ) - 1 ) lQ 0))
  **  (Int64Array.missing_i Q (((i - j ) - j ) - 1 ) 0 ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((A + (j * sizeof(INT64)))) # Int64  |-> (Znth j lA 0))
  **  (Int64Array.missing_i A j 0 (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) lBrow )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((A + (j * sizeof(INT64)))) # Int64  |-> (Znth j lA 0))
  **  (Int64Array.missing_i A j 0 (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_19 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) lBrow )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_20 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) < 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((A + (j * sizeof(INT64)))) # Int64  |-> (Znth j lA 0))
  **  (Int64Array.missing_i A j 0 (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_21 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) < 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) lBrow )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_22 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) < 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((A + (j * sizeof(INT64)))) # Int64  |-> (Znth j lA 0))
  **  (Int64Array.missing_i A j 0 (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_23 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) < 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) lBrow )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_24 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX)) (PreH4 : ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN)) (PreH5 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH6 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH7 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH8 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH9 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH10 : (blocked <= INT64_MAX)) (PreH11 : (m_pre <= INT64_MAX)) (PreH12 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH13 : (blocked >= INT64_MIN)) (PreH14 : (m_pre >= INT64_MIN)) (PreH15 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (n_pre <= INT_MAX)) (PreH19 : ((i - j ) <= INT_MAX)) (PreH20 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : ((i - j ) >= INT_MIN)) (PreH25 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH26 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH27 : (j < i)) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 5000)) (PreH30 : (10 <= m_pre)) (PreH31 : (m_pre <= 1000000000)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= i)) (PreH36 : (0 <= blocked)) (PreH37 : (blocked < m_pre)) (PreH38 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH39 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH40 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH41 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH42 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH43 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH44 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH45 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH46 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH47 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ ((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |-> (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0))
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_25 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (0 <= (((i - j ) - j ) - 1 ))) (PreH2 : ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 ))) (PreH3 : (blocked <= INT64_MAX)) (PreH4 : (m_pre <= INT64_MAX)) (PreH5 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH6 : (blocked >= INT64_MIN)) (PreH7 : (m_pre >= INT64_MIN)) (PreH8 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (n_pre <= INT_MAX)) (PreH12 : ((i - j ) <= INT_MAX)) (PreH13 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH14 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN)) (PreH21 : ((((i - j ) - j ) - 1 ) >= 0)) (PreH22 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH23 : (j < i)) (PreH24 : (1 <= n_pre)) (PreH25 : (n_pre <= 5000)) (PreH26 : (10 <= m_pre)) (PreH27 : (m_pre <= 1000000000)) (PreH28 : (1 <= i)) (PreH29 : (i <= n_pre)) (PreH30 : (1 <= j)) (PreH31 : (j <= i)) (PreH32 : (0 <= blocked)) (PreH33 : (blocked < m_pre)) (PreH34 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH35 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH36 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH37 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH38 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH40 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH41 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH42 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH43 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (0 <= (((i - j ) - j ) - 1 )) ” 
  &&  “ ((((i - j ) - j ) - 1 ) < ((2 * n_pre ) + 4 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= INT_MIN) ” 
  &&  “ ((((i - j ) - j ) - 1 ) >= 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |-> (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0))
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((1 % ( m_pre ) ) + (Znth (((i - j ) - j ) - 1 ) lQ 0) ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_26 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ))) (PreH3 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 ))) (PreH4 : (blocked <= INT64_MAX)) (PreH5 : (m_pre <= INT64_MAX)) (PreH6 : ((1 % ( m_pre ) ) <= INT64_MAX)) (PreH7 : (blocked >= INT64_MIN)) (PreH8 : (m_pre >= INT64_MIN)) (PreH9 : ((1 % ( m_pre ) ) >= INT64_MIN)) (PreH10 : (j <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : ((i - j ) <= INT_MAX)) (PreH14 : (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX)) (PreH15 : (j >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (n_pre >= INT_MIN)) (PreH18 : ((i - j ) >= INT_MIN)) (PreH19 : (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN)) (PreH20 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1)) (PreH21 : (j < i)) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 5000)) (PreH24 : (10 <= m_pre)) (PreH25 : (m_pre <= 1000000000)) (PreH26 : (1 <= i)) (PreH27 : (i <= n_pre)) (PreH28 : (1 <= j)) (PreH29 : (j <= i)) (PreH30 : (0 <= blocked)) (PreH31 : (blocked < m_pre)) (PreH32 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH33 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH34 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH35 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH36 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH38 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH39 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH40 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH41 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) < 0) ” 
  &&  “ (0 <= ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) )) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < (n_pre + 1 )) ” 
  &&  “ (blocked <= INT64_MAX) ” 
  &&  “ (m_pre <= INT64_MAX) ” 
  &&  “ ((1 % ( m_pre ) ) <= INT64_MAX) ” 
  &&  “ (blocked >= INT64_MIN) ” 
  &&  “ (m_pre >= INT64_MIN) ” 
  &&  “ ((1 % ( m_pre ) ) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((i - j ) <= INT_MAX) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ ((i - j ) >= INT_MIN) ” 
  &&  “ (((((i - j ) + j ) + 2 ) ÷ 2 ) >= INT_MIN) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) >= 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |-> (Znth j (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0))
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (((((1 % ( m_pre ) ) + (Znth ((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) lpow2 0) ) - (1 % ( m_pre ) ) ) + m_pre ) % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_27 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : ((((i - j ) - j ) - 1 ) < 0)) (PreH2 : (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1)) (PreH3 : (j < i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= j)) (PreH11 : (j <= i)) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH15 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH16 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH17 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH18 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH20 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH21 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH22 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH23 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full Brow (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((((i - j ) - j ) - 1 ) < 0) ” 
  &&  “ (((i - j ) - ((((i - j ) + j ) + 2 ) ÷ 2 ) ) < 1) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((Brow + (j * sizeof(INT64)))) # Int64  |-> (Znth j (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) 0))
  **  (Int64Array.missing_i Brow j 0 (n_pre + 2 ) (replace_Znth (j) ((((Znth j lA 0) * (1 % ( m_pre ) ) ) % ( m_pre ) )) (lBrow)) )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_28 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (j >= i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((pow2 + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (i - 1 ) lpow2 0))
  **  (Int64Array.missing_i pow2 (i - 1 ) 0 (n_pre + 1 ) lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_29 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (blocked: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= i)) (PreH10 : (0 <= blocked)) (PreH11 : (blocked < m_pre)) (PreH12 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH13 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH14 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH15 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH17 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH18 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH19 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH20 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 ))))) (PreH21 : forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) ,
  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (j >= i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((j - 1 )))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < j)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ”
  &&  (((A + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i A i 0 (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_30 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (q < i) ” 
  &&  “ (q <> 0) ” 
  &&  “ (q <= i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) (q))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((Brow + (q * sizeof(INT64)))) # Int64  |-> (Znth q lBrow 0))
  **  (Int64Array.missing_i Brow q 0 (n_pre + 2 ) lBrow )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_31 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (q >= i) ” 
  &&  “ (q <> 0) ” 
  &&  “ (q <= i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) (q))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((A + (i * sizeof(INT64)))) # Int64  |-> (Znth i lA 0))
  **  (Int64Array.missing_i A i 0 (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_32 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q = 0)) (PreH2 : (q <= i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= q)) (PreH10 : (q <= (i + 1 ))) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH25 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH26 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (q = 0) ” 
  &&  “ (q <= i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) (q))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((P + (q * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i P q 0 (n_pre + 2 ) lP )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
.

Definition solver_partial_solve_wit_33 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q < i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (q < i) ” 
  &&  “ (q <> 0) ” 
  &&  “ (q <= i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) (q))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((P + (q * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i P q 0 (n_pre + 2 ) lP )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
.

Definition solver_partial_solve_wit_34 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (q: Z) (i: Z) (PreH1 : (q >= i)) (PreH2 : (q <> 0)) (PreH3 : (q <= i)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5000)) (PreH6 : (10 <= m_pre)) (PreH7 : (m_pre <= 1000000000)) (PreH8 : (1 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (0 <= q)) (PreH11 : (q <= (i + 1 ))) (PreH12 : (0 <= blocked)) (PreH13 : (blocked < m_pre)) (PreH14 : (0 <= run)) (PreH15 : (run < m_pre)) (PreH16 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH17 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH18 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH19 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH20 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH22 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH23 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) (PreH24 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH25 : (run = (RowRun (m_pre) (n_pre) (i) (q)))) (PreH26 : forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj))))) (PreH27 : forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (q >= i) ” 
  &&  “ (q <> 0) ” 
  &&  “ (q <= i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q <= (i + 1 )) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) (q))) ” 
  &&  “ forall (jj: Z) , (((1 <= jj) /\ (jj < i)) -> ((Znth (jj) (lBrow) (0)) = (RowBrow (m_pre) (n_pre) (i) (jj)))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq < q)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((P + (q * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i P q 0 (n_pre + 2 ) lP )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
.

Definition solver_partial_solve_wit_35 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i + t ) <= (2 * n_pre )) ” 
  &&  “ (t < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (QPartial (m_pre) (n_pre) (i) (t))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 )))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((Q + ((i + t ) * sizeof(INT64)))) # Int64  |-> (Znth (i + t ) lQ 0))
  **  (Int64Array.missing_i Q (i + t ) 0 ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_36 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ ((i + t ) <= (2 * n_pre )) ” 
  &&  “ (t < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (QPartial (m_pre) (n_pre) (i) (t))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 )))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((P + (t * sizeof(INT64)))) # Int64  |-> (Znth t lP 0))
  **  (Int64Array.missing_i P t 0 (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
.

Definition solver_partial_solve_wit_37 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (run: Z) (blocked: Z) (t: Z) (i: Z) (PreH1 : ((i + t ) <= (2 * n_pre ))) (PreH2 : (t < i)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5000)) (PreH5 : (10 <= m_pre)) (PreH6 : (m_pre <= 1000000000)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= t)) (PreH10 : (t <= i)) (PreH11 : (0 <= blocked)) (PreH12 : (blocked < m_pre)) (PreH13 : (0 <= run)) (PreH14 : (run < m_pre)) (PreH15 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH16 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH17 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH18 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH19 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH21 : (lA = (DPA (m_pre) (n_pre) (i)))) (PreH22 : (lQ = (QPartial (m_pre) (n_pre) (i) (t)))) (PreH23 : (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 ))))) (PreH24 : (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 ))))) (PreH25 : forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq))))) ,
  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
|--
  “ ((i + t ) <= (2 * n_pre )) ” 
  &&  “ (t < i) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= i) ” 
  &&  “ (0 <= blocked) ” 
  &&  “ (blocked < m_pre) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run < m_pre) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (i))) ” 
  &&  “ (lQ = (QPartial (m_pre) (n_pre) (i) (t))) ” 
  &&  “ (blocked = (RowBlocked (m_pre) (n_pre) (i) ((i - 1 )))) ” 
  &&  “ (run = (RowRun (m_pre) (n_pre) (i) ((i + 1 )))) ” 
  &&  “ forall (qq: Z) , (((0 <= qq) /\ (qq <= i)) -> ((Znth (qq) (lP) (0)) = (RowP (m_pre) (n_pre) (i) (qq)))) ”
  &&  (((Q + ((i + t ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i Q (i + t ) 0 ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full P (n_pre + 2 ) lP )
  **  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
.

Definition solver_partial_solve_wit_38 := 
forall (m_pre: Z) (n_pre: Z) (P: Z) (Brow: Z) (Q: Z) (pow2: Z) (A: Z) (lP: (@list Z)) (lBrow: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lA: (@list Z)) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : (1 <= i)) (PreH7 : (i <= (n_pre + 1 ))) (PreH8 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH9 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH10 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH11 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH12 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre))))) (PreH14 : (lA = (DPA (m_pre) (n_pre) ((i - 1 ))))) (PreH15 : (lQ = (DPQ (m_pre) (n_pre) ((i - 1 ))))) ,
  (Int64Array.full A (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
|--
  “ (i > n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (n_pre + 1 ))) -> ((Znth (k) (lpow2) (0)) = (Pow2Mod (k) (m_pre)))) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) ((i - 1 )))) ” 
  &&  “ (lQ = (DPQ (m_pre) (n_pre) ((i - 1 )))) ”
  &&  (((A + (n_pre * sizeof(INT64)))) # Int64  |-> (Znth n_pre lA 0))
  **  (Int64Array.missing_i A n_pre 0 (n_pre + 2 ) lA )
  **  (Int64Array.full pow2 (n_pre + 1 ) lpow2 )
  **  (Int64Array.undef_seg pow2 (n_pre + 1 ) (n_pre + 2 ) )
  **  (Int64Array.full Q ((2 * n_pre ) + 4 ) lQ )
  **  (Int64Array.full Brow (n_pre + 2 ) lBrow )
  **  (Int64Array.full P (n_pre + 2 ) lP )
.

Definition solver_partial_solve_wit_39_pure := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (A: Z) (Q: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  (Int64Array.mixed_full A (Zlength (cA)) cA )
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.mixed_full Q (Zlength (cQ)) cQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lA))))) ” 
  &&  “ ((Zlength ((SomeList (lA)))) = (Zlength ((SomeList (lA))))) ”
.

Definition solver_partial_solve_wit_39_aux := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (A: Z) (Q: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  (Int64Array.mixed_full A (Zlength (cA)) cA )
  **  (Int64Array.mixed_full Q (Zlength (cQ)) cQ )
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lA))))) ” 
  &&  “ ((Zlength ((SomeList (lA)))) = (Zlength ((SomeList (lA))))) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (n_pre))) ” 
  &&  “ (ans = (Znth (n_pre) (lA) (0))) ” 
  &&  “ (Spec n_pre m_pre ans ) ” 
  &&  “ (cA = (SomeList (lA))) ” 
  &&  “ (cQ = (SomeList (lQ))) ” 
  &&  “ (cpow2 = (SomeListUndefTail (lpow2))) ” 
  &&  “ (cBrow = (SomeList (lBrow))) ” 
  &&  “ (cP = (SomeList (lP))) ” 
  &&  “ ((Zlength (cA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (cpow2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cP)) = (n_pre + 2 )) ”
  &&  (Int64Array.mixed_full A (Zlength ((SomeList (lA)))) (SomeList (lA)) )
  **  (Int64Array.mixed_full Q (Zlength (cQ)) cQ )
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
.

Definition solver_partial_solve_wit_39 := solver_partial_solve_wit_39_pure -> solver_partial_solve_wit_39_aux.

Definition solver_partial_solve_wit_40_pure := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (A: Z) (Q: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  (Int64Array.mixed_full Q (Zlength (cQ)) cQ )
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lQ))))) ” 
  &&  “ ((Zlength ((SomeList (lQ)))) = (Zlength ((SomeList (lQ))))) ”
.

Definition solver_partial_solve_wit_40_aux := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (Q: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  (Int64Array.mixed_full Q (Zlength (cQ)) cQ )
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lQ))))) ” 
  &&  “ ((Zlength ((SomeList (lQ)))) = (Zlength ((SomeList (lQ))))) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (n_pre))) ” 
  &&  “ (ans = (Znth (n_pre) (lA) (0))) ” 
  &&  “ (Spec n_pre m_pre ans ) ” 
  &&  “ (cA = (SomeList (lA))) ” 
  &&  “ (cQ = (SomeList (lQ))) ” 
  &&  “ (cpow2 = (SomeListUndefTail (lpow2))) ” 
  &&  “ (cBrow = (SomeList (lBrow))) ” 
  &&  “ (cP = (SomeList (lP))) ” 
  &&  “ ((Zlength (cA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (cpow2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cP)) = (n_pre + 2 )) ”
  &&  (Int64Array.mixed_full Q (Zlength ((SomeList (lQ)))) (SomeList (lQ)) )
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
.

Definition solver_partial_solve_wit_40 := solver_partial_solve_wit_40_pure -> solver_partial_solve_wit_40_aux.

Definition solver_partial_solve_wit_41_pure := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (A: Z) (Q: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeListUndefTail (lpow2))))) ” 
  &&  “ ((Zlength ((SomeListUndefTail (lpow2)))) = (Zlength ((SomeListUndefTail (lpow2))))) ”
.

Definition solver_partial_solve_wit_41_aux := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  (Int64Array.mixed_full pow2 (Zlength (cpow2)) cpow2 )
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeListUndefTail (lpow2))))) ” 
  &&  “ ((Zlength ((SomeListUndefTail (lpow2)))) = (Zlength ((SomeListUndefTail (lpow2))))) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (n_pre))) ” 
  &&  “ (ans = (Znth (n_pre) (lA) (0))) ” 
  &&  “ (Spec n_pre m_pre ans ) ” 
  &&  “ (cA = (SomeList (lA))) ” 
  &&  “ (cQ = (SomeList (lQ))) ” 
  &&  “ (cpow2 = (SomeListUndefTail (lpow2))) ” 
  &&  “ (cBrow = (SomeList (lBrow))) ” 
  &&  “ (cP = (SomeList (lP))) ” 
  &&  “ ((Zlength (cA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (cpow2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cP)) = (n_pre + 2 )) ”
  &&  (Int64Array.mixed_full pow2 (Zlength ((SomeListUndefTail (lpow2)))) (SomeListUndefTail (lpow2)) )
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
.

Definition solver_partial_solve_wit_41 := solver_partial_solve_wit_41_pure -> solver_partial_solve_wit_41_aux.

Definition solver_partial_solve_wit_42_pure := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (A: Z) (Q: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lBrow))))) ” 
  &&  “ ((Zlength ((SomeList (lBrow)))) = (Zlength ((SomeList (lBrow))))) ”
.

Definition solver_partial_solve_wit_42_aux := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  (Int64Array.mixed_full Brow (Zlength (cBrow)) cBrow )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lBrow))))) ” 
  &&  “ ((Zlength ((SomeList (lBrow)))) = (Zlength ((SomeList (lBrow))))) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (n_pre))) ” 
  &&  “ (ans = (Znth (n_pre) (lA) (0))) ” 
  &&  “ (Spec n_pre m_pre ans ) ” 
  &&  “ (cA = (SomeList (lA))) ” 
  &&  “ (cQ = (SomeList (lQ))) ” 
  &&  “ (cpow2 = (SomeListUndefTail (lpow2))) ” 
  &&  “ (cBrow = (SomeList (lBrow))) ” 
  &&  “ (cP = (SomeList (lP))) ” 
  &&  “ ((Zlength (cA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (cpow2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cP)) = (n_pre + 2 )) ”
  &&  (Int64Array.mixed_full Brow (Zlength ((SomeList (lBrow)))) (SomeList (lBrow)) )
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
.

Definition solver_partial_solve_wit_42 := solver_partial_solve_wit_42_pure -> solver_partial_solve_wit_42_aux.

Definition solver_partial_solve_wit_43_pure := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (A: Z) (Q: Z) (pow2: Z) (Brow: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int64  |-> m_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int64  |-> ans)
  **  ((( &( "A" ) )) # Ptr  |-> A)
  **  ((( &( "Q" ) )) # Ptr  |-> Q)
  **  ((( &( "pow2" ) )) # Ptr  |-> pow2)
  **  ((( &( "Brow" ) )) # Ptr  |-> Brow)
  **  ((( &( "P" ) )) # Ptr  |-> P)
  **  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lP))))) ” 
  &&  “ ((Zlength ((SomeList (lP)))) = (Zlength ((SomeList (lP))))) ”
.

Definition solver_partial_solve_wit_43_aux := 
forall (m_pre: Z) (n_pre: Z) (lA: (@list Z)) (lQ: (@list Z)) (lpow2: (@list Z)) (lBrow: (@list Z)) (lP: (@list Z)) (cA: (@list (@option Z))) (cQ: (@list (@option Z))) (cpow2: (@list (@option Z))) (cBrow: (@list (@option Z))) (cP: (@list (@option Z))) (i: Z) (ans: Z) (P: Z) (PreH1 : (i = (n_pre + 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5000)) (PreH4 : (10 <= m_pre)) (PreH5 : (m_pre <= 1000000000)) (PreH6 : ((Zlength (lA)) = (n_pre + 2 ))) (PreH7 : ((Zlength (lQ)) = ((2 * n_pre ) + 4 ))) (PreH8 : ((Zlength (lpow2)) = (n_pre + 1 ))) (PreH9 : ((Zlength (lBrow)) = (n_pre + 2 ))) (PreH10 : ((Zlength (lP)) = (n_pre + 2 ))) (PreH11 : (lA = (DPA (m_pre) (n_pre) (n_pre)))) (PreH12 : (ans = (Znth (n_pre) (lA) (0)))) (PreH13 : (Spec n_pre m_pre ans )) (PreH14 : (cA = (SomeList (lA)))) (PreH15 : (cQ = (SomeList (lQ)))) (PreH16 : (cpow2 = (SomeListUndefTail (lpow2)))) (PreH17 : (cBrow = (SomeList (lBrow)))) (PreH18 : (cP = (SomeList (lP)))) (PreH19 : ((Zlength (cA)) = (n_pre + 2 ))) (PreH20 : ((Zlength (cQ)) = ((2 * n_pre ) + 4 ))) (PreH21 : ((Zlength (cpow2)) = (n_pre + 2 ))) (PreH22 : ((Zlength (cBrow)) = (n_pre + 2 ))) (PreH23 : ((Zlength (cP)) = (n_pre + 2 ))) ,
  (Int64Array.mixed_full P (Zlength (cP)) cP )
|--
  “ (0 <= (Zlength ((SomeList (lP))))) ” 
  &&  “ ((Zlength ((SomeList (lP)))) = (Zlength ((SomeList (lP))))) ” 
  &&  “ (i = (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5000) ” 
  &&  “ (10 <= m_pre) ” 
  &&  “ (m_pre <= 1000000000) ” 
  &&  “ ((Zlength (lA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (lpow2)) = (n_pre + 1 )) ” 
  &&  “ ((Zlength (lBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (lP)) = (n_pre + 2 )) ” 
  &&  “ (lA = (DPA (m_pre) (n_pre) (n_pre))) ” 
  &&  “ (ans = (Znth (n_pre) (lA) (0))) ” 
  &&  “ (Spec n_pre m_pre ans ) ” 
  &&  “ (cA = (SomeList (lA))) ” 
  &&  “ (cQ = (SomeList (lQ))) ” 
  &&  “ (cpow2 = (SomeListUndefTail (lpow2))) ” 
  &&  “ (cBrow = (SomeList (lBrow))) ” 
  &&  “ (cP = (SomeList (lP))) ” 
  &&  “ ((Zlength (cA)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cQ)) = ((2 * n_pre ) + 4 )) ” 
  &&  “ ((Zlength (cpow2)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cBrow)) = (n_pre + 2 )) ” 
  &&  “ ((Zlength (cP)) = (n_pre + 2 )) ”
  &&  (Int64Array.mixed_full P (Zlength ((SomeList (lP)))) (SomeList (lP)) )
.

Definition solver_partial_solve_wit_43 := solver_partial_solve_wit_43_pure -> solver_partial_solve_wit_43_aux.

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
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Axiom proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Axiom proof_of_solver_safety_wit_59 : solver_safety_wit_59.
Axiom proof_of_solver_safety_wit_60 : solver_safety_wit_60.
Axiom proof_of_solver_safety_wit_61 : solver_safety_wit_61.
Axiom proof_of_solver_safety_wit_62 : solver_safety_wit_62.
Axiom proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Axiom proof_of_solver_safety_wit_64 : solver_safety_wit_64.
Axiom proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Axiom proof_of_solver_safety_wit_66 : solver_safety_wit_66.
Axiom proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Axiom proof_of_solver_safety_wit_68 : solver_safety_wit_68.
Axiom proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Axiom proof_of_solver_safety_wit_70 : solver_safety_wit_70.
Axiom proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Axiom proof_of_solver_safety_wit_72 : solver_safety_wit_72.
Axiom proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Axiom proof_of_solver_safety_wit_74 : solver_safety_wit_74.
Axiom proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Axiom proof_of_solver_safety_wit_76 : solver_safety_wit_76.
Axiom proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Axiom proof_of_solver_safety_wit_78 : solver_safety_wit_78.
Axiom proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Axiom proof_of_solver_safety_wit_80 : solver_safety_wit_80.
Axiom proof_of_solver_safety_wit_81 : solver_safety_wit_81.
Axiom proof_of_solver_safety_wit_82 : solver_safety_wit_82.
Axiom proof_of_solver_safety_wit_83 : solver_safety_wit_83.
Axiom proof_of_solver_safety_wit_84 : solver_safety_wit_84.
Axiom proof_of_solver_safety_wit_85 : solver_safety_wit_85.
Axiom proof_of_solver_safety_wit_86 : solver_safety_wit_86.
Axiom proof_of_solver_safety_wit_87 : solver_safety_wit_87.
Axiom proof_of_solver_safety_wit_88 : solver_safety_wit_88.
Axiom proof_of_solver_safety_wit_89 : solver_safety_wit_89.
Axiom proof_of_solver_safety_wit_90 : solver_safety_wit_90.
Axiom proof_of_solver_safety_wit_91 : solver_safety_wit_91.
Axiom proof_of_solver_safety_wit_92 : solver_safety_wit_92.
Axiom proof_of_solver_safety_wit_93 : solver_safety_wit_93.
Axiom proof_of_solver_safety_wit_94 : solver_safety_wit_94.
Axiom proof_of_solver_safety_wit_95 : solver_safety_wit_95.
Axiom proof_of_solver_safety_wit_96 : solver_safety_wit_96.
Axiom proof_of_solver_safety_wit_97 : solver_safety_wit_97.
Axiom proof_of_solver_safety_wit_98 : solver_safety_wit_98.
Axiom proof_of_solver_safety_wit_99 : solver_safety_wit_99.
Axiom proof_of_solver_safety_wit_100 : solver_safety_wit_100.
Axiom proof_of_solver_safety_wit_101 : solver_safety_wit_101.
Axiom proof_of_solver_safety_wit_102 : solver_safety_wit_102.
Axiom proof_of_solver_safety_wit_103 : solver_safety_wit_103.
Axiom proof_of_solver_safety_wit_104 : solver_safety_wit_104.
Axiom proof_of_solver_safety_wit_105 : solver_safety_wit_105.
Axiom proof_of_solver_safety_wit_106 : solver_safety_wit_106.
Axiom proof_of_solver_safety_wit_107 : solver_safety_wit_107.
Axiom proof_of_solver_safety_wit_108 : solver_safety_wit_108.
Axiom proof_of_solver_safety_wit_109 : solver_safety_wit_109.
Axiom proof_of_solver_safety_wit_110 : solver_safety_wit_110.
Axiom proof_of_solver_safety_wit_111 : solver_safety_wit_111.
Axiom proof_of_solver_safety_wit_112 : solver_safety_wit_112.
Axiom proof_of_solver_safety_wit_113 : solver_safety_wit_113.
Axiom proof_of_solver_safety_wit_114 : solver_safety_wit_114.
Axiom proof_of_solver_safety_wit_115 : solver_safety_wit_115.
Axiom proof_of_solver_safety_wit_116 : solver_safety_wit_116.
Axiom proof_of_solver_safety_wit_117 : solver_safety_wit_117.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Axiom proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Axiom proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Axiom proof_of_solver_entail_wit_18 : solver_entail_wit_18.
Axiom proof_of_solver_entail_wit_19 : solver_entail_wit_19.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
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
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.
Axiom proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34.
Axiom proof_of_solver_partial_solve_wit_35 : solver_partial_solve_wit_35.
Axiom proof_of_solver_partial_solve_wit_36 : solver_partial_solve_wit_36.
Axiom proof_of_solver_partial_solve_wit_37 : solver_partial_solve_wit_37.
Axiom proof_of_solver_partial_solve_wit_38 : solver_partial_solve_wit_38.
Axiom proof_of_solver_partial_solve_wit_39_pure : solver_partial_solve_wit_39_pure.
Axiom proof_of_solver_partial_solve_wit_39 : solver_partial_solve_wit_39.
Axiom proof_of_solver_partial_solve_wit_40_pure : solver_partial_solve_wit_40_pure.
Axiom proof_of_solver_partial_solve_wit_40 : solver_partial_solve_wit_40.
Axiom proof_of_solver_partial_solve_wit_41_pure : solver_partial_solve_wit_41_pure.
Axiom proof_of_solver_partial_solve_wit_41 : solver_partial_solve_wit_41.
Axiom proof_of_solver_partial_solve_wit_42_pure : solver_partial_solve_wit_42_pure.
Axiom proof_of_solver_partial_solve_wit_42 : solver_partial_solve_wit_42.
Axiom proof_of_solver_partial_solve_wit_43_pure : solver_partial_solve_wit_43_pure.
Axiom proof_of_solver_partial_solve_wit_43 : solver_partial_solve_wit_43.

End VC_Correct.
