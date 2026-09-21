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
Require Import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib.
Local Open Scope sac.

(*----- Function matrixChainMinCost -----*)

Definition matrixChainMinCost_safety_wit_1 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (Forall (Z.le (1)) dimensions_l )) (PreH6 : (Forall (Z.ge (100)) dimensions_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  (IntArray.undef_full ( &( "cost" ) ) 64 )
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition matrixChainMinCost_safety_wit_2 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (i: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH6 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH7 : (Forall (Z.le (1)) dimensions_l )) (PreH8 : (Forall (Z.ge (100)) dimensions_l )) (PreH9 : ((Zlength (cost_l)) = i)) (PreH10 : (Forall (eq (0)) cost_l )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 i cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((matrix_count_pre * matrix_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (matrix_count_pre * matrix_count_pre )) ”
.

Definition matrixChainMinCost_safety_wit_3 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (eq (0)) cost_l )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 i cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition matrixChainMinCost_safety_wit_4 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (eq (0)) cost_l )) ,
  (IntArray.seg ( &( "cost" ) ) 0 (i + 1 ) (app (cost_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (i + 1 ) (matrix_count_pre * matrix_count_pre ) )
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_5 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (i: Z) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (eq (0)) cost_l )) ,
  ((( &( "chain_length" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 i cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition matrixChainMinCost_safety_wit_6 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition matrixChainMinCost_safety_wit_7 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH5 : (2 <= chain_length)) (PreH6 : (chain_length <= matrix_count_pre)) (PreH7 : (0 <= left)) (PreH8 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH9 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH10 : (Forall (Z.le (1)) dimensions_l )) (PreH11 : (Forall (Z.ge (100)) dimensions_l )) (PreH12 : (Forall (Z.le (0)) cost_l )) (PreH13 : (Forall (Z.ge (7000000)) cost_l )) (PreH14 : (1 <= chain_length)) (PreH15 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left + chain_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + chain_length )) ”
.

Definition matrixChainMinCost_safety_wit_8 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l )) (PreH14 : (Forall (Z.ge (7000000)) cost_l )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((left + chain_length ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + chain_length ) - 1 )) ”
.

Definition matrixChainMinCost_safety_wit_9 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l )) (PreH14 : (Forall (Z.ge (7000000)) cost_l )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left + chain_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + chain_length )) ”
.

Definition matrixChainMinCost_safety_wit_10 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l )) (PreH14 : (Forall (Z.ge (7000000)) cost_l )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_11 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) )) ”
.

Definition matrixChainMinCost_safety_wit_12 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) )) ”
.

Definition matrixChainMinCost_safety_wit_13 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((right + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_14 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) )) ”
.

Definition matrixChainMinCost_safety_wit_15 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_16 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) )) ”
.

Definition matrixChainMinCost_safety_wit_17 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((((left + 1 ) * matrix_count_pre ) + right ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((left + 1 ) * matrix_count_pre ) + right )) ”
.

Definition matrixChainMinCost_safety_wit_18 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((left + 1 ) * matrix_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + 1 ) * matrix_count_pre )) ”
.

Definition matrixChainMinCost_safety_wit_19 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_20 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((left * matrix_count_pre ) + left ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left * matrix_count_pre ) + left )) ”
.

Definition matrixChainMinCost_safety_wit_21 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left * matrix_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * matrix_count_pre )) ”
.

Definition matrixChainMinCost_safety_wit_22 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_23 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_24 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_25 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "split" ) )) # Int  |->_)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |-> (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ))
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_26 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "split" ) )) # Int  |->_)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "best" ) )) # Int  |-> (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ))
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_27 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) )) ”
.

Definition matrixChainMinCost_safety_wit_28 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) )) ”
.

Definition matrixChainMinCost_safety_wit_29 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((right + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_30 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) )) ”
.

Definition matrixChainMinCost_safety_wit_31 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_32 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) )) ”
.

Definition matrixChainMinCost_safety_wit_33 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((((split + 1 ) * matrix_count_pre ) + right ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((split + 1 ) * matrix_count_pre ) + right )) ”
.

Definition matrixChainMinCost_safety_wit_34 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((split + 1 ) * matrix_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((split + 1 ) * matrix_count_pre )) ”
.

Definition matrixChainMinCost_safety_wit_35 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_36 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((left * matrix_count_pre ) + split ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left * matrix_count_pre ) + split )) ”
.

Definition matrixChainMinCost_safety_wit_37 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left * matrix_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * matrix_count_pre )) ”
.

Definition matrixChainMinCost_safety_wit_38 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_39 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_40 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_safety_wit_41 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l )) (PreH23 : (Forall (Z.ge (7000000)) cost_l )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> candidate)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_42 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l )) (PreH23 : (Forall (Z.ge (7000000)) cost_l )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_43 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l )) (PreH20 : (Forall (Z.ge (7000000)) cost_l )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (((left * matrix_count_pre ) + right ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left * matrix_count_pre ) + right )) ”
.

Definition matrixChainMinCost_safety_wit_44 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l )) (PreH20 : (Forall (Z.ge (7000000)) cost_l )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left * matrix_count_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * matrix_count_pre )) ”
.

Definition matrixChainMinCost_safety_wit_45 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l )) (PreH20 : (Forall (Z.ge (7000000)) cost_l )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) (replace_Znth (((left * matrix_count_pre ) + right )) (best) (cost_l)) )
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_46 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : ((left + chain_length ) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l )) (PreH14 : (Forall (Z.ge (7000000)) cost_l )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "chain_length" ) )) # Int  |-> chain_length)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((chain_length + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (chain_length + 1 )) ”
.

Definition matrixChainMinCost_safety_wit_47 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ ((matrix_count_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (matrix_count_pre - 1 )) ”
.

Definition matrixChainMinCost_safety_wit_48 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "dimensions" ) )) # Ptr  |-> dimensions_pre)
  **  ((( &( "matrix_count" ) )) # Int  |-> matrix_count_pre)
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition matrixChainMinCost_entail_wit_1 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (Forall (Z.le (1)) dimensions_l )) (PreH6 : (Forall (Z.ge (100)) dimensions_l )) ,
  (IntArray.undef_full ( &( "cost" ) ) 64 )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ ((Zlength (cost_l)) = 0) ” 
  &&  “ (Forall (eq (0)) cost_l ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 0 cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) 0 (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (Forall (Z.le (1)) dimensions_l )) (PreH6 : (Forall (Z.ge (100)) dimensions_l )) ,
  (IntArray.undef_full ( &( "cost" ) ) 64 )
|--
  “ (Forall (eq (0)) (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (IntArray.undef_seg ( &( "cost" ) ) 0 (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
).

Definition matrixChainMinCost_entail_wit_1_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (Forall (Z.le (1)) dimensions_l )) (PreH6 : (Forall (Z.ge (100)) dimensions_l )) ,
  (IntArray.undef_full ( &( "cost" ) ) 64 )
|--
  “ (Forall (eq (0)) (@nil Z) ) ”
.

Definition matrixChainMinCost_entail_wit_1_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (Forall (Z.le (1)) dimensions_l )) (PreH6 : (Forall (Z.ge (100)) dimensions_l )) ,
  (IntArray.undef_full ( &( "cost" ) ) 64 )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition matrixChainMinCost_entail_wit_1_split_goal_spatial := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (Forall (Z.le (1)) dimensions_l )) (PreH6 : (Forall (Z.ge (100)) dimensions_l )) ,
  (IntArray.undef_full ( &( "cost" ) ) 64 )
|--
  (IntArray.undef_seg ( &( "cost" ) ) 0 (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_entail_wit_2 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (eq (0)) cost_l_2 )) ,
  (IntArray.seg ( &( "cost" ) ) 0 (i + 1 ) (app (cost_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (i + 1 ) (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ ((Zlength (cost_l)) = (i + 1 )) ” 
  &&  “ (Forall (eq (0)) cost_l ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 (i + 1 ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (i + 1 ) (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (eq (0)) cost_l_2 )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (app (cost_l_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (cost_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_2_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (eq (0)) cost_l_2 )) ,
  (Forall (eq (0)) (app (cost_l_2) ((cons (0) ((@nil Z))))) )
.

Definition matrixChainMinCost_entail_wit_2_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (eq (0)) cost_l_2 )) ,
  ((Zlength ((app (cost_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition matrixChainMinCost_entail_wit_3 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (eq (0)) cost_l_2 )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 i cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= 2) ” 
  &&  “ (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre 2 ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (eq (0)) cost_l_2 )) ,
  (IntArray.seg ( &( "cost" ) ) 0 i cost_l_2 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= 2) ” 
  &&  “ (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre 2 ) ”
  &&  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
).

Definition matrixChainMinCost_entail_wit_4 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l_2 )) (PreH12 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((matrix_count_pre - chain_length ) + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length 0 ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l_2 )) (PreH12 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  TT && emp 
|--
  “ (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length 0 ) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_4_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l_2 )) (PreH12 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length 0 )
.

Definition matrixChainMinCost_entail_wit_5 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (((left + chain_length ) - 1 ) = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < ((left + chain_length ) - 1 )) ” 
  &&  “ (((left + chain_length ) - 1 ) < matrix_count_pre) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + left )) ” 
  &&  “ (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) ” 
  &&  “ ((((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (((left + chain_length ) - 1 ) + 1 )) ” 
  &&  “ ((((left + chain_length ) - 1 ) + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0)) ” 
  &&  “ ((Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (left + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (left + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  TT && emp 
|--
  “ ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (left + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (left + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + left ) cost_l_2 0) <= 7000000) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l_2 0)) ” 
  &&  “ ((((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_5_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100)
.

Definition matrixChainMinCost_entail_wit_5_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0))
.

Definition matrixChainMinCost_entail_wit_5_split_goal_3 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth (left + 1 ) dimensions_l 0) <= 100)
.

Definition matrixChainMinCost_entail_wit_5_split_goal_4 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (1 <= (Znth (left + 1 ) dimensions_l 0))
.

Definition matrixChainMinCost_entail_wit_5_split_goal_5 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth left dimensions_l 0) <= 100)
.

Definition matrixChainMinCost_entail_wit_5_split_goal_6 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (1 <= (Znth left dimensions_l 0))
.

Definition matrixChainMinCost_entail_wit_5_split_goal_7 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <= 7000000)
.

Definition matrixChainMinCost_entail_wit_5_split_goal_8 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0))
.

Definition matrixChainMinCost_entail_wit_5_split_goal_9 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth ((left * matrix_count_pre ) + left ) cost_l_2 0) <= 7000000)
.

Definition matrixChainMinCost_entail_wit_5_split_goal_10 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l_2 0))
.

Definition matrixChainMinCost_entail_wit_5_split_goal_11 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre ))
.

Definition matrixChainMinCost_entail_wit_5_split_goal_12 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))
.

Definition matrixChainMinCost_entail_wit_6 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l_2: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= right) ” 
  &&  “ (0 <= (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) )) ” 
  &&  “ ((((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ) <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l_2 ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l_2 ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (left + 1 ) (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ) ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  TT && emp 
|--
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1 ) (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) ) ” 
  &&  “ ((((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <= 7000000) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_6_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1 ) (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) )
.

Definition matrixChainMinCost_entail_wit_6_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <= 7000000)
.

Definition matrixChainMinCost_entail_wit_7 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + split )) ” 
  &&  “ (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((split + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (split + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (split + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  TT && emp 
|--
  “ ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (split + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (split + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + split ) cost_l_2 0) <= 7000000) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l_2 0)) ” 
  &&  “ ((((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_7_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100)
.

Definition matrixChainMinCost_entail_wit_7_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0))
.

Definition matrixChainMinCost_entail_wit_7_split_goal_3 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth (split + 1 ) dimensions_l 0) <= 100)
.

Definition matrixChainMinCost_entail_wit_7_split_goal_4 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (1 <= (Znth (split + 1 ) dimensions_l 0))
.

Definition matrixChainMinCost_entail_wit_7_split_goal_5 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth left dimensions_l 0) <= 100)
.

Definition matrixChainMinCost_entail_wit_7_split_goal_6 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (1 <= (Znth left dimensions_l 0))
.

Definition matrixChainMinCost_entail_wit_7_split_goal_7 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <= 7000000)
.

Definition matrixChainMinCost_entail_wit_7_split_goal_8 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0))
.

Definition matrixChainMinCost_entail_wit_7_split_goal_9 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth ((left * matrix_count_pre ) + split ) cost_l_2 0) <= 7000000)
.

Definition matrixChainMinCost_entail_wit_7_split_goal_10 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l_2 0))
.

Definition matrixChainMinCost_entail_wit_7_split_goal_11 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre ))
.

Definition matrixChainMinCost_entail_wit_7_split_goal_12 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))
.

Definition matrixChainMinCost_entail_wit_8 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l_2: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ (0 <= (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) )) ” 
  &&  “ ((((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ) <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l_2 ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l_2 ) ” 
  &&  “ (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (right + 1 ) dimensions_l 0) ) ) ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  TT && emp 
|--
  “ (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length ) - 1 ) split (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) ) ” 
  &&  “ ((((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <= 7000000) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_8_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length ) - 1 ) split (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) )
.

Definition matrixChainMinCost_entail_wit_8_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <= 7000000)
.

Definition matrixChainMinCost_entail_wit_9_1 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l_2 )) (PreH23 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (split + 1 ) candidate ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l_2 )) (PreH23 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  TT && emp 
|--
  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1 ) candidate ) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_9_1_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l_2 )) (PreH23 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1 ) candidate )
.

Definition matrixChainMinCost_entail_wit_9_2 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l_2 )) (PreH23 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (split + 1 ) best ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l_2 )) (PreH23 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  TT && emp 
|--
  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1 ) best ) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_9_2_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH20 : (Forall (Z.le (1)) dimensions_l )) (PreH21 : (Forall (Z.ge (100)) dimensions_l )) (PreH22 : (Forall (Z.le (0)) cost_l_2 )) (PreH23 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1 ) best )
.

Definition matrixChainMinCost_entail_wit_10 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + right )) ” 
  &&  “ (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best ) ” 
  &&  “ (MatrixChainIntervalMinimum dimensions_l left right best ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  TT && emp 
|--
  “ (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length ) - 1 ) best ) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length ) - 1 ) best ) ” 
  &&  “ (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre )) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_10_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length ) - 1 ) best )
.

Definition matrixChainMinCost_entail_wit_10_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length ) - 1 ) best )
.

Definition matrixChainMinCost_entail_wit_10_split_goal_3 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : (Forall (Z.le (1)) dimensions_l )) (PreH19 : (Forall (Z.ge (100)) dimensions_l )) (PreH20 : (Forall (Z.le (0)) cost_l_2 )) (PreH21 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre ))
.

Definition matrixChainMinCost_entail_wit_11 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l_2 )) (PreH20 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) (replace_Znth (((left * matrix_count_pre ) + right )) (best) (cost_l_2)) )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= ((matrix_count_pre - chain_length ) + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length (left + 1 ) ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l_2 )) (PreH20 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  TT && emp 
|--
  “ (MatrixChainLeftComplete dimensions_l (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1 ) ) ” 
  &&  “ (Forall (Z.ge (7000000)) (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre )) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_11_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l_2 )) (PreH20 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (MatrixChainLeftComplete dimensions_l (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1 ) )
.

Definition matrixChainMinCost_entail_wit_11_split_goal_2 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l_2 )) (PreH20 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (Forall (Z.ge (7000000)) (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) )
.

Definition matrixChainMinCost_entail_wit_11_split_goal_3 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l_2 )) (PreH20 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (Forall (Z.le (0)) (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) )
.

Definition matrixChainMinCost_entail_wit_11_split_goal_4 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l_2 )) (PreH20 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  ((Zlength ((replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre ))
.

Definition matrixChainMinCost_entail_wit_12 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l_2 )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (2 <= (chain_length + 1 )) ” 
  &&  “ ((chain_length + 1 ) <= (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= (chain_length + 1 )) ” 
  &&  “ (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre (chain_length + 1 ) ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  TT && emp 
|--
  “ (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre (chain_length + 1 ) ) ”
  &&  emp
).

Definition matrixChainMinCost_entail_wit_12_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) dimensions_l )) (PreH12 : (Forall (Z.ge (100)) dimensions_l )) (PreH13 : (Forall (Z.le (0)) cost_l_2 )) (PreH14 : (Forall (Z.ge (7000000)) cost_l_2 )) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre (chain_length + 1 ) )
.

Definition matrixChainMinCost_entail_wit_13 := 
(
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  ((( &( "width" ) )) # Int  |-> matrix_count_pre)
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1 ) cost_l 0) ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_full ( &( "cost" ) ) 64 )
  **  ((( &( "width" ) )) # Int  |->_)
) \/
(
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1 ) cost_l 0) ) ”
  &&  (IntArray.undef_full ( &( "cost" ) ) 64 )
).

Definition matrixChainMinCost_entail_wit_13_split_goal_1 := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1 ) cost_l 0) ) ”
.

Definition matrixChainMinCost_entail_wit_13_split_goal_spatial := 
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  (IntArray.undef_full ( &( "cost" ) ) 64 )
.

Definition matrixChainMinCost_return_wit_1 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (result: Z) (PreH1 : (MatrixChainOptimalCost dimensions_l matrix_count_pre result )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre result ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
.

Definition matrixChainMinCost_partial_solve_wit_1 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH8 : (Forall (Z.le (1)) dimensions_l )) (PreH9 : (Forall (Z.ge (100)) dimensions_l )) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (eq (0)) cost_l )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 i cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (i < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ ((Zlength (cost_l)) = i) ” 
  &&  “ (Forall (eq (0)) cost_l ) ”
  &&  (((( &( "cost" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "cost" ) ) (i + 1 ) (matrix_count_pre * matrix_count_pre ) )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg ( &( "cost" ) ) 0 i cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_2 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + left )) ” 
  &&  “ (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((left + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (left + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (left + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left ) ”
  &&  (((( &( "cost" ) ) + (((left * matrix_count_pre ) + left ) * sizeof(INT)))) # Int  |-> (Znth ((left * matrix_count_pre ) + left ) cost_l 0))
  **  (IntArray.missing_i ( &( "cost" ) ) ((left * matrix_count_pre ) + left ) 0 (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_3 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + left )) ” 
  &&  “ (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((left + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (left + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (left + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left ) ”
  &&  (((( &( "cost" ) ) + ((((left + 1 ) * matrix_count_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))
  **  (IntArray.missing_i ( &( "cost" ) ) (((left + 1 ) * matrix_count_pre ) + right ) 0 (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_4 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + left )) ” 
  &&  “ (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((left + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (left + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (left + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left ) ”
  &&  (((dimensions_pre + (left * sizeof(INT)))) # Int  |-> (Znth left dimensions_l 0))
  **  (IntArray.missing_i dimensions_pre left 0 (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_5 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + left )) ” 
  &&  “ (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((left + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (left + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (left + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left ) ”
  &&  (((dimensions_pre + ((left + 1 ) * sizeof(INT)))) # Int  |-> (Znth (left + 1 ) dimensions_l 0))
  **  (IntArray.missing_i dimensions_pre (left + 1 ) 0 (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_6 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) dimensions_l )) (PreH34 : (Forall (Z.ge (100)) dimensions_l )) (PreH35 : (Forall (Z.le (0)) cost_l )) (PreH36 : (Forall (Z.ge (7000000)) cost_l )) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + left )) ” 
  &&  “ (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((left + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (left + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (left + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left ) ”
  &&  (((dimensions_pre + ((right + 1 ) * sizeof(INT)))) # Int  |-> (Znth (right + 1 ) dimensions_l 0))
  **  (IntArray.missing_i dimensions_pre (right + 1 ) 0 (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_7 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + split )) ” 
  &&  “ (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((split + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (split + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (split + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best ) ”
  &&  (((( &( "cost" ) ) + (((left * matrix_count_pre ) + split ) * sizeof(INT)))) # Int  |-> (Znth ((left * matrix_count_pre ) + split ) cost_l 0))
  **  (IntArray.missing_i ( &( "cost" ) ) ((left * matrix_count_pre ) + split ) 0 (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_8 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + split )) ” 
  &&  “ (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((split + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (split + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (split + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best ) ”
  &&  (((( &( "cost" ) ) + ((((split + 1 ) * matrix_count_pre ) + right ) * sizeof(INT)))) # Int  |-> (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))
  **  (IntArray.missing_i ( &( "cost" ) ) (((split + 1 ) * matrix_count_pre ) + right ) 0 (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_9 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + split )) ” 
  &&  “ (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((split + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (split + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (split + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best ) ”
  &&  (((dimensions_pre + (left * sizeof(INT)))) # Int  |-> (Znth left dimensions_l 0))
  **  (IntArray.missing_i dimensions_pre left 0 (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_10 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + split )) ” 
  &&  “ (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((split + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (split + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (split + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best ) ”
  &&  (((dimensions_pre + ((split + 1 ) * sizeof(INT)))) # Int  |-> (Znth (split + 1 ) dimensions_l 0))
  **  (IntArray.missing_i dimensions_pre (split + 1 ) 0 (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_11 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH37 : (Forall (Z.le (1)) dimensions_l )) (PreH38 : (Forall (Z.ge (100)) dimensions_l )) (PreH39 : (Forall (Z.le (0)) cost_l )) (PreH40 : (Forall (Z.ge (7000000)) cost_l )) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ ((left + 1 ) <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + split )) ” 
  &&  “ (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (((split + 1 ) * matrix_count_pre ) + right )) ” 
  &&  “ ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < (matrix_count_pre + 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0)) ” 
  &&  “ ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000) ” 
  &&  “ (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0)) ” 
  &&  “ ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000) ” 
  &&  “ (1 <= (Znth left dimensions_l 0)) ” 
  &&  “ ((Znth left dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (split + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (split + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ (1 <= (Znth (right + 1 ) dimensions_l 0)) ” 
  &&  “ ((Znth (right + 1 ) dimensions_l 0) <= 100) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best ) ”
  &&  (((dimensions_pre + ((right + 1 ) * sizeof(INT)))) # Int  |-> (Znth (right + 1 ) dimensions_l 0))
  **  (IntArray.missing_i dimensions_pre (right + 1 ) 0 (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_12 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH17 : (Forall (Z.le (1)) dimensions_l )) (PreH18 : (Forall (Z.ge (100)) dimensions_l )) (PreH19 : (Forall (Z.le (0)) cost_l )) (PreH20 : (Forall (Z.ge (7000000)) cost_l )) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best )) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= matrix_count_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ ((left + chain_length ) <= matrix_count_pre) ” 
  &&  “ (right = ((left + chain_length ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (right < matrix_count_pre) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7000000) ” 
  &&  “ (0 <= ((left * matrix_count_pre ) + right )) ” 
  &&  “ (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best ) ” 
  &&  “ (MatrixChainIntervalMinimum dimensions_l left right best ) ”
  &&  (((( &( "cost" ) ) + (((left * matrix_count_pre ) + right ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cost" ) ) ((left * matrix_count_pre ) + right ) 0 (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Definition matrixChainMinCost_partial_solve_wit_13 := 
forall (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) dimensions_l )) (PreH10 : (Forall (Z.ge (100)) dimensions_l )) (PreH11 : (Forall (Z.le (0)) cost_l )) (PreH12 : (Forall (Z.ge (7000000)) cost_l )) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
|--
  “ (chain_length > matrix_count_pre) ” 
  &&  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (2 <= chain_length) ” 
  &&  “ (chain_length <= (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) dimensions_l ) ” 
  &&  “ (Forall (Z.ge (100)) dimensions_l ) ” 
  &&  “ (Forall (Z.le (0)) cost_l ) ” 
  &&  “ (Forall (Z.ge (7000000)) cost_l ) ” 
  &&  “ (1 <= chain_length) ” 
  &&  “ (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length ) ”
  &&  (((( &( "cost" ) ) + ((matrix_count_pre - 1 ) * sizeof(INT)))) # Int  |-> (Znth (matrix_count_pre - 1 ) cost_l 0))
  **  (IntArray.missing_i ( &( "cost" ) ) (matrix_count_pre - 1 ) 0 (matrix_count_pre * matrix_count_pre ) cost_l )
  **  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre ) 64 )
.

Module Type VC_Correct.


Axiom proof_of_matrixChainMinCost_safety_wit_1 : matrixChainMinCost_safety_wit_1.
Axiom proof_of_matrixChainMinCost_safety_wit_2 : matrixChainMinCost_safety_wit_2.
Axiom proof_of_matrixChainMinCost_safety_wit_3 : matrixChainMinCost_safety_wit_3.
Axiom proof_of_matrixChainMinCost_safety_wit_4 : matrixChainMinCost_safety_wit_4.
Axiom proof_of_matrixChainMinCost_safety_wit_5 : matrixChainMinCost_safety_wit_5.
Axiom proof_of_matrixChainMinCost_safety_wit_6 : matrixChainMinCost_safety_wit_6.
Axiom proof_of_matrixChainMinCost_safety_wit_7 : matrixChainMinCost_safety_wit_7.
Axiom proof_of_matrixChainMinCost_safety_wit_8 : matrixChainMinCost_safety_wit_8.
Axiom proof_of_matrixChainMinCost_safety_wit_9 : matrixChainMinCost_safety_wit_9.
Axiom proof_of_matrixChainMinCost_safety_wit_10 : matrixChainMinCost_safety_wit_10.
Axiom proof_of_matrixChainMinCost_safety_wit_11 : matrixChainMinCost_safety_wit_11.
Axiom proof_of_matrixChainMinCost_safety_wit_12 : matrixChainMinCost_safety_wit_12.
Axiom proof_of_matrixChainMinCost_safety_wit_13 : matrixChainMinCost_safety_wit_13.
Axiom proof_of_matrixChainMinCost_safety_wit_14 : matrixChainMinCost_safety_wit_14.
Axiom proof_of_matrixChainMinCost_safety_wit_15 : matrixChainMinCost_safety_wit_15.
Axiom proof_of_matrixChainMinCost_safety_wit_16 : matrixChainMinCost_safety_wit_16.
Axiom proof_of_matrixChainMinCost_safety_wit_17 : matrixChainMinCost_safety_wit_17.
Axiom proof_of_matrixChainMinCost_safety_wit_18 : matrixChainMinCost_safety_wit_18.
Axiom proof_of_matrixChainMinCost_safety_wit_19 : matrixChainMinCost_safety_wit_19.
Axiom proof_of_matrixChainMinCost_safety_wit_20 : matrixChainMinCost_safety_wit_20.
Axiom proof_of_matrixChainMinCost_safety_wit_21 : matrixChainMinCost_safety_wit_21.
Axiom proof_of_matrixChainMinCost_safety_wit_22 : matrixChainMinCost_safety_wit_22.
Axiom proof_of_matrixChainMinCost_safety_wit_23 : matrixChainMinCost_safety_wit_23.
Axiom proof_of_matrixChainMinCost_safety_wit_24 : matrixChainMinCost_safety_wit_24.
Axiom proof_of_matrixChainMinCost_safety_wit_25 : matrixChainMinCost_safety_wit_25.
Axiom proof_of_matrixChainMinCost_safety_wit_26 : matrixChainMinCost_safety_wit_26.
Axiom proof_of_matrixChainMinCost_safety_wit_27 : matrixChainMinCost_safety_wit_27.
Axiom proof_of_matrixChainMinCost_safety_wit_28 : matrixChainMinCost_safety_wit_28.
Axiom proof_of_matrixChainMinCost_safety_wit_29 : matrixChainMinCost_safety_wit_29.
Axiom proof_of_matrixChainMinCost_safety_wit_30 : matrixChainMinCost_safety_wit_30.
Axiom proof_of_matrixChainMinCost_safety_wit_31 : matrixChainMinCost_safety_wit_31.
Axiom proof_of_matrixChainMinCost_safety_wit_32 : matrixChainMinCost_safety_wit_32.
Axiom proof_of_matrixChainMinCost_safety_wit_33 : matrixChainMinCost_safety_wit_33.
Axiom proof_of_matrixChainMinCost_safety_wit_34 : matrixChainMinCost_safety_wit_34.
Axiom proof_of_matrixChainMinCost_safety_wit_35 : matrixChainMinCost_safety_wit_35.
Axiom proof_of_matrixChainMinCost_safety_wit_36 : matrixChainMinCost_safety_wit_36.
Axiom proof_of_matrixChainMinCost_safety_wit_37 : matrixChainMinCost_safety_wit_37.
Axiom proof_of_matrixChainMinCost_safety_wit_38 : matrixChainMinCost_safety_wit_38.
Axiom proof_of_matrixChainMinCost_safety_wit_39 : matrixChainMinCost_safety_wit_39.
Axiom proof_of_matrixChainMinCost_safety_wit_40 : matrixChainMinCost_safety_wit_40.
Axiom proof_of_matrixChainMinCost_safety_wit_41 : matrixChainMinCost_safety_wit_41.
Axiom proof_of_matrixChainMinCost_safety_wit_42 : matrixChainMinCost_safety_wit_42.
Axiom proof_of_matrixChainMinCost_safety_wit_43 : matrixChainMinCost_safety_wit_43.
Axiom proof_of_matrixChainMinCost_safety_wit_44 : matrixChainMinCost_safety_wit_44.
Axiom proof_of_matrixChainMinCost_safety_wit_45 : matrixChainMinCost_safety_wit_45.
Axiom proof_of_matrixChainMinCost_safety_wit_46 : matrixChainMinCost_safety_wit_46.
Axiom proof_of_matrixChainMinCost_safety_wit_47 : matrixChainMinCost_safety_wit_47.
Axiom proof_of_matrixChainMinCost_safety_wit_48 : matrixChainMinCost_safety_wit_48.
Axiom proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1.
Axiom proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2.
Axiom proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3.
Axiom proof_of_matrixChainMinCost_entail_wit_4 : matrixChainMinCost_entail_wit_4.
Axiom proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5.
Axiom proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6.
Axiom proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7.
Axiom proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8.
Axiom proof_of_matrixChainMinCost_entail_wit_9_1 : matrixChainMinCost_entail_wit_9_1.
Axiom proof_of_matrixChainMinCost_entail_wit_9_2 : matrixChainMinCost_entail_wit_9_2.
Axiom proof_of_matrixChainMinCost_entail_wit_10 : matrixChainMinCost_entail_wit_10.
Axiom proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11.
Axiom proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12.
Axiom proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13.
Axiom proof_of_matrixChainMinCost_return_wit_1 : matrixChainMinCost_return_wit_1.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_1 : matrixChainMinCost_partial_solve_wit_1.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_2 : matrixChainMinCost_partial_solve_wit_2.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_3 : matrixChainMinCost_partial_solve_wit_3.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_4 : matrixChainMinCost_partial_solve_wit_4.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_5 : matrixChainMinCost_partial_solve_wit_5.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_6 : matrixChainMinCost_partial_solve_wit_6.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_7 : matrixChainMinCost_partial_solve_wit_7.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_8 : matrixChainMinCost_partial_solve_wit_8.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_9 : matrixChainMinCost_partial_solve_wit_9.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_10 : matrixChainMinCost_partial_solve_wit_10.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_11 : matrixChainMinCost_partial_solve_wit_11.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_12 : matrixChainMinCost_partial_solve_wit_12.
Axiom proof_of_matrixChainMinCost_partial_solve_wit_13 : matrixChainMinCost_partial_solve_wit_13.

End VC_Correct.
