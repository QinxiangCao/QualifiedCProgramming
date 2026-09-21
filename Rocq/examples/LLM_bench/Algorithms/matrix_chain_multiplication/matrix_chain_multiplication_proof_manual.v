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
From SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication Require Import matrix_chain_multiplication_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib.
Local Open Scope sac.
Require Import AUXLib.MonotonicList.
(* Proofs reused by the current witnesses, kept with their mathematical
   statements in this manual so they compile without a separate library. *)
Module ReusedProof.
Definition matrixChainMinCost_entail_wit_1_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH4 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) ,
  (MatrixChainZeroPrefix (@nil Z) 0 ).

Definition matrixChainMinCost_entail_wit_2_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i < (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i )) ,
  (MatrixChainZeroPrefix (app (cost_l_2) ((cons (0) ((@nil Z))))) (i + 1 ) ).

Definition matrixChainMinCost_entail_wit_3 :=
(
forall (cost_pre: Z) (matrix_count_pre: Z) (dimensions_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i )) ,
  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.seg cost_pre 0 i cost_l_2 )
  **  (IntArray.undef_seg cost_pre i (matrix_count_pre * matrix_count_pre ) )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre ) ” 
  &&  “ (MatrixChainTableValuesBounded cost_l ) ” 
  &&  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre 2 ) ”
  &&  (IntArray.full dimensions_pre (matrix_count_pre + 1 ) dimensions_l )
  **  (IntArray.full cost_pre (matrix_count_pre * matrix_count_pre ) cost_l )
) \/
(
forall (cost_pre: Z) (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (i: Z) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre ))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) (PreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH8 : (MatrixChainZeroPrefix cost_l_2 i )) ,
  (IntArray.seg cost_pre 0 i cost_l_2 )
|--
  EX (cost_l: (@list Z)) ,
  “ (1 <= matrix_count_pre) ” 
  &&  “ (matrix_count_pre <= 8) ” 
  &&  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1 )) ” 
  &&  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre )) ” 
  &&  “ (MatrixChainDimensionsBounded dimensions_l matrix_count_pre ) ” 
  &&  “ (MatrixChainTableValuesBounded cost_l ) ” 
  &&  “ (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre 2 ) ”
  &&  (IntArray.full cost_pre (matrix_count_pre * matrix_count_pre ) cost_l )
).

Definition matrixChainMinCost_entail_wit_5_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH9 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length 0 ).

Definition matrixChainMinCost_entail_wit_6_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100).

Definition matrixChainMinCost_entail_wit_6_split_goal_2 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0)).

Definition matrixChainMinCost_entail_wit_6_split_goal_3 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth (left + 1 ) dimensions_l 0) <= 100).

Definition matrixChainMinCost_entail_wit_6_split_goal_4 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (1 <= (Znth (left + 1 ) dimensions_l 0)).

Definition matrixChainMinCost_entail_wit_6_split_goal_5 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth left dimensions_l 0) <= 100).

Definition matrixChainMinCost_entail_wit_6_split_goal_6 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (1 <= (Znth left dimensions_l 0)).

Definition matrixChainMinCost_entail_wit_6_split_goal_7 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <= 7000000).

Definition matrixChainMinCost_entail_wit_6_split_goal_8 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0)).

Definition matrixChainMinCost_entail_wit_6_split_goal_9 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((Znth ((left * matrix_count_pre ) + left ) cost_l_2 0) <= 7000000).

Definition matrixChainMinCost_entail_wit_6_split_goal_10 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l_2 0)).

Definition matrixChainMinCost_entail_wit_6_split_goal_11 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  ((((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre )).

Definition matrixChainMinCost_entail_wit_6_split_goal_12 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre )).

Definition matrixChainMinCost_entail_wit_7_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH33 : (MatrixChainTableValuesBounded cost_l )) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left )) ,
  (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1 ) (((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) ).

Definition matrixChainMinCost_entail_wit_7_split_goal_2 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= ((left * matrix_count_pre ) + left ))) (PreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) (PreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) (PreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= left)) (PreH15 : (left < (matrix_count_pre + 1 ))) (PreH16 : (0 <= (left + 1 ))) (PreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (right + 1 ))) (PreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) (PreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) (PreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l 0))) (PreH27 : ((Znth left dimensions_l 0) <= 100)) (PreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) (PreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) (PreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH33 : (MatrixChainTableValuesBounded cost_l )) (PreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left )) ,
  ((((Znth ((left * matrix_count_pre ) + left ) cost_l 0) + (Znth (((left + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (left + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <= 7000000).

Definition matrixChainMinCost_entail_wit_8_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) <= 100).

Definition matrixChainMinCost_entail_wit_8_split_goal_2 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (1 <= (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0)).

Definition matrixChainMinCost_entail_wit_8_split_goal_3 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth (split + 1 ) dimensions_l 0) <= 100).

Definition matrixChainMinCost_entail_wit_8_split_goal_4 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (1 <= (Znth (split + 1 ) dimensions_l 0)).

Definition matrixChainMinCost_entail_wit_8_split_goal_5 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth left dimensions_l 0) <= 100).

Definition matrixChainMinCost_entail_wit_8_split_goal_6 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (1 <= (Znth left dimensions_l 0)).

Definition matrixChainMinCost_entail_wit_8_split_goal_7 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0) <= 7000000).

Definition matrixChainMinCost_entail_wit_8_split_goal_8 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l_2 0)).

Definition matrixChainMinCost_entail_wit_8_split_goal_9 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((Znth ((left * matrix_count_pre ) + split ) cost_l_2 0) <= 7000000).

Definition matrixChainMinCost_entail_wit_8_split_goal_10 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l_2 0)).

Definition matrixChainMinCost_entail_wit_8_split_goal_11 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre )).

Definition matrixChainMinCost_entail_wit_8_split_goal_12 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre )).

Definition matrixChainMinCost_entail_wit_9_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH37 : (MatrixChainTableValuesBounded cost_l )) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length ) - 1 ) split (((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) ).

Definition matrixChainMinCost_entail_wit_9_split_goal_2 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1 ) <= split)) (PreH11 : (split < right)) (PreH12 : (0 <= ((left * matrix_count_pre ) + split ))) (PreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) (PreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH16 : (0 <= left)) (PreH17 : (left < (matrix_count_pre + 1 ))) (PreH18 : (0 <= (split + 1 ))) (PreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) (PreH20 : (0 <= (right + 1 ))) (PreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) (PreH22 : (0 <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) (PreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) (PreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) (PreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) (PreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l 0))) (PreH31 : ((Znth left dimensions_l 0) <= 100)) (PreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) (PreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) (PreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) (PreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) (PreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH37 : (MatrixChainTableValuesBounded cost_l )) (PreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) ,
  ((((Znth ((left * matrix_count_pre ) + split ) cost_l 0) + (Znth (((split + 1 ) * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) cost_l 0) ) + (((Znth left dimensions_l 0) * (Znth (split + 1 ) dimensions_l 0) ) * (Znth (((left + chain_length ) - 1 ) + 1 ) dimensions_l 0) ) ) <= 7000000).

Definition matrixChainMinCost_entail_wit_10_1_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH20 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1 ) candidate ).

Definition matrixChainMinCost_entail_wit_10_2_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (split: Z) (best: Z) (candidate: Z) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split < right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : (0 <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH20 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) (PreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1 ) best ).

Definition matrixChainMinCost_entail_wit_11_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length ) - 1 ) best ).

Definition matrixChainMinCost_entail_wit_11_split_goal_2 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length ) - 1 ) best ).

Definition matrixChainMinCost_entail_wit_11_split_goal_3 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (chain_length: Z) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : (0 <= left)) (PreH7 : ((left + chain_length ) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length ) - 1 ))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1 ) <= split)) (PreH12 : (split <= right)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH18 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) ,
  (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) ) < (matrix_count_pre * matrix_count_pre )).

Definition matrixChainMinCost_entail_wit_12_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH17 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (MatrixChainLeftProgress dimensions_l (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1 ) ).

Definition matrixChainMinCost_entail_wit_12_split_goal_2 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH17 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  (MatrixChainTableValuesBounded (replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)) ).

Definition matrixChainMinCost_entail_wit_12_split_goal_3 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (cost_l_2: (@list Z)) (chain_length: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : (0 <= left)) (PreH6 : ((left + chain_length ) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length ) - 1 ))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7000000)) (PreH12 : (0 <= ((left * matrix_count_pre ) + right ))) (PreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH17 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) (PreH19 : (MatrixChainIntervalMinimum dimensions_l left right best )) ,
  ((Zlength ((replace_Znth (((left * matrix_count_pre ) + ((left + chain_length ) - 1 ) )) (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre )).

Definition matrixChainMinCost_entail_wit_13_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (left: Z) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : ((left + chain_length ) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : (0 <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) (PreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH11 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) ,
  (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (chain_length + 1 ) ).

Definition matrixChainMinCost_entail_wit_14_split_goal_1 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH9 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  (MatrixChainMinimumCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1 ) cost_l_2 0) ).

Definition matrixChainMinCost_entail_wit_14_split_goal_2 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH9 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  (MatrixChainTableResult dimensions_l cost_l_2 matrix_count_pre ).

Definition matrixChainMinCost_entail_wit_14_split_goal_3 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH9 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre (matrix_count_pre + 1 ) ).

Definition matrixChainMinCost_entail_wit_14_split_goal_4 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH9 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  ((Znth (matrix_count_pre - 1 ) cost_l_2 0) <= 7000000).

Definition matrixChainMinCost_entail_wit_14_split_goal_5 :=
forall (matrix_count_pre: Z) (dimensions_l: (@list Z)) (chain_length: Z) (cost_l_2: (@list Z)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1 ))) (PreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) (PreH9 : (MatrixChainTableValuesBounded cost_l_2 )) (PreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length )) ,
  (0 <= (Znth (matrix_count_pre - 1 ) cost_l_2 0)).

Lemma proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 : matrixChainMinCost_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainZeroPrefix.
  split.
  - reflexivity.
  - intros index Hindex. lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 : matrixChainMinCost_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainZeroPrefix in *.
  destruct PreH8 as [Hlength Hzero].
  split.
  - rewrite Zlength_app, Hlength. reflexivity.
  - intros index Hindex.
    destruct (Z_lt_ge_dec index i) as [Hlt | Hge].
    + rewrite app_Znth1.
      * apply Hzero. lia.
      * lia.
    + assert (index = i) by lia. subst index.
      rewrite app_Znth2.
      * rewrite Hlength. replace (i - i) with 0 by lia.
        rewrite Znth0_cons. reflexivity.
      * lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = matrix_count_pre * matrix_count_pre) by lia.
  subst i.
  destruct PreH8 as [Htable Hzero].
  Exists cost_l_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic
      (IntArray.seg_to_full cost_pre 0
         (matrix_count_pre * matrix_count_pre) cost_l_2).
    cancel (IntArray.full dimensions_pre
              (matrix_count_pre + 1) dimensions_l).
    replace (cost_pre + 0 * sizeof(INT)) with cost_pre by lia.
    replace (matrix_count_pre * matrix_count_pre - 0)
      with (matrix_count_pre * matrix_count_pre) by lia.
    cancel (IntArray.full cost_pre
              (matrix_count_pre * matrix_count_pre) cost_l_2).
  - split_pures.
    + dump_pre_spatial. exact PreH2.
    + dump_pre_spatial. exact PreH3.
    + dump_pre_spatial. exact PreH4.
    + dump_pre_spatial. exact Htable.
    + dump_pre_spatial. exact PreH7.
    + dump_pre_spatial.
      unfold MatrixChainTableValuesBounded.
      intros index Hindex.
      rewrite Hzero by lia. lia.
    + dump_pre_spatial.
      apply matrix_chain_zero_table_lengths_done__initialization.
      * exact PreH2.
      * exact PreH4.
      * split; assumption.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 : matrixChainMinCost_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainLeftProgress.
  split.
  - exact PreH10.
  - intros left right Hleft. lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 : matrixChainMinCost_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 : matrixChainMinCost_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_3 : matrixChainMinCost_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (left + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_4 : matrixChainMinCost_entail_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound (left + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_5 : matrixChainMinCost_entail_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_6 : matrixChainMinCost_entail_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH10.
  destruct PreH10 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_7 : matrixChainMinCost_entail_wit_6_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11
    (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_8 : matrixChainMinCost_entail_wit_6_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11
    (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_9 : matrixChainMinCost_entail_wit_6_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11 (left * matrix_count_pre + left)
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_10 : matrixChainMinCost_entail_wit_6_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH11.
  specialize (PreH11 (left * matrix_count_pre + left)
    ltac:(rewrite PreH5; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_11 : matrixChainMinCost_entail_wit_6_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.mul_le_mono_nonneg_r (left + 1) (matrix_count_pre - 1)
    matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
  rewrite Z.mul_sub_distr_r in Hrow. lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_6_split_goal_12 : matrixChainMinCost_entail_wit_6_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.mul_le_mono_nonneg_r left (matrix_count_pre - 1)
    matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
  rewrite Z.mul_sub_distr_r in Hrow. lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 : matrixChainMinCost_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply matrix_chain_split_progress_initial__candidate_progress.
  exact PreH34.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 : matrixChainMinCost_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainLeftProgress in PreH34.
  destruct PreH34 as [Hlengths _].
  unfold MatrixChainLengthsDone in Hlengths.
  destruct Hlengths as [_ Hdone].
  assert (Hleft_minimum :
    MatrixChainIntervalMinimum dimensions_l left left
      (Znth (left * matrix_count_pre + left) cost_l 0)).
  {
    eapply Hdone with (length := 1); lia.
  }
  assert (Hright_minimum :
    MatrixChainIntervalMinimum dimensions_l (left + 1)
      (left + chain_length - 1)
      (Znth ((left + 1) * matrix_count_pre +
             (left + chain_length - 1)) cost_l 0)).
  {
    eapply Hdone with (length := chain_length - 1); lia.
  }
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre left left
       (Znth (left * matrix_count_pre + left) cost_l 0)
       PreH32 ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
    as Hleft_bound.
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre (left + 1)
       (left + chain_length - 1)
       (Znth ((left + 1) * matrix_count_pre +
              (left + chain_length - 1)) cost_l 0)
       PreH32 ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
    as Hright_bound.
  assert (Htwo_dimensions :
    Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0 <= 10000)
    by nia.
  assert (Hlast_lower :
    1 <= Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH30.
  }
  assert (Hlast_upper :
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 100).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH31.
  }
  assert (Hproduct_step :
    (Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0) *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <=
    10000 * Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    apply Z.mul_le_mono_nonneg_r; lia.
  }
  assert (Hproduct :
    Znth left dimensions_l 0 * Znth (left + 1) dimensions_l 0 *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 1000000)
    by lia.
  nia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 : matrixChainMinCost_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 : matrixChainMinCost_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (((left + chain_length) - 1) + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_3 : matrixChainMinCost_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (split + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_4 : matrixChainMinCost_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound (split + 1) ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_5 : matrixChainMinCost_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_6 : matrixChainMinCost_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainDimensionsBounded in PreH17.
  destruct PreH17 as [_ Hbound].
  specialize (Hbound left ltac:(lia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_7 : matrixChainMinCost_entail_wit_8_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18
    (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_8 : matrixChainMinCost_entail_wit_8_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18
    (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1))
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_9 : matrixChainMinCost_entail_wit_8_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18 (left * matrix_count_pre + split)
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_10 : matrixChainMinCost_entail_wit_8_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH18.
  specialize (PreH18 (left * matrix_count_pre + split)
    ltac:(rewrite PreH16; nia)).
  lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_11 : matrixChainMinCost_entail_wit_8_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.mul_le_mono_nonneg_r (split + 1) (matrix_count_pre - 1)
    matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
  rewrite Z.mul_sub_distr_r in Hrow. lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_8_split_goal_12 : matrixChainMinCost_entail_wit_8_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.mul_le_mono_nonneg_r left (matrix_count_pre - 1)
    matrix_count_pre ltac:(lia) ltac:(lia)) as Hrow.
  rewrite Z.mul_sub_distr_r in Hrow. lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_9_split_goal_1 : matrixChainMinCost_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_9_split_goal_2 : matrixChainMinCost_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainSplitProgress in PreH38.
  destruct PreH38 as [Hleft_progress _].
  unfold MatrixChainLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlengths _].
  unfold MatrixChainLengthsDone in Hlengths.
  destruct Hlengths as [_ Hdone].
  assert (Hleft_minimum :
    MatrixChainIntervalMinimum dimensions_l left split
      (Znth (left * matrix_count_pre + split) cost_l 0)).
  {
    eapply Hdone with (length := split - left + 1); lia.
  }
  assert (Hright_minimum :
    MatrixChainIntervalMinimum dimensions_l (split + 1)
      (left + chain_length - 1)
      (Znth ((split + 1) * matrix_count_pre +
             (left + chain_length - 1)) cost_l 0)).
  {
    eapply Hdone with (length := left + chain_length - split - 1); lia.
  }
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre left split
       (Znth (left * matrix_count_pre + split) cost_l 0)
       PreH36 ltac:(lia) ltac:(lia) ltac:(lia) Hleft_minimum)
    as Hleft_bound.
  pose proof
    (matrix_chain_interval_minimum_upper_bound__candidate_progress
       dimensions_l matrix_count_pre (split + 1)
       (left + chain_length - 1)
       (Znth ((split + 1) * matrix_count_pre +
              (left + chain_length - 1)) cost_l 0)
       PreH36 ltac:(lia) ltac:(lia) ltac:(lia) Hright_minimum)
    as Hright_bound.
  assert (Htwo_dimensions :
    Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0 <= 10000)
    by nia.
  assert (Hlast_lower :
    1 <= Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH34.
  }
  assert (Hlast_upper :
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 100).
  {
    replace ((left + chain_length - 1) + 1) with (right + 1) by lia.
    exact PreH35.
  }
  assert (Hproduct_step :
    (Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0) *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <=
    10000 * Znth ((left + chain_length - 1) + 1) dimensions_l 0).
  {
    apply Z.mul_le_mono_nonneg_r; lia.
  }
  assert (Hproduct :
    Znth left dimensions_l 0 * Znth (split + 1) dimensions_l 0 *
    Znth ((left + chain_length - 1) + 1) dimensions_l 0 <= 1000000)
    by lia.
  nia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1 : matrixChainMinCost_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH21.
  apply (matrix_chain_split_progress_better__min_update
    dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length
    left split best candidate);
    [lia | lia | exact PreH21 | exact PreH22].
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1 : matrixChainMinCost_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH8 in PreH21.
  apply (matrix_chain_split_progress_not_better__min_update
    dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length
    left split best candidate);
    [lia | lia | exact PreH21 | exact PreH22].
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 : matrixChainMinCost_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (matrix_chain_split_progress_complete__min_update
    dimensions_l cost_l_2 matrix_count_pre chain_length left
    (left + chain_length - 1) best).
  - exact PreH4.
  - exact PreH6.
  - reflexivity.
  - lia.
  - lia.
  - replace (left + chain_length - 1) with split by lia.
    exact PreH19.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 : matrixChainMinCost_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (left + chain_length - 1) with split by lia.
  exact PreH19.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 : matrixChainMinCost_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  nia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 : matrixChainMinCost_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcurrent :
      0 <= left * matrix_count_pre + (left + chain_length - 1) <
           Zlength cost_l_2).
  { rewrite PreH15. rewrite <- PreH7. lia. }
  unfold MatrixChainSplitProgress in PreH18.
  destruct PreH18 as [Hprogress _].
  unfold MatrixChainLeftProgress in *.
  destruct Hprogress as [Hlengths Hleft].
  split.
  - unfold MatrixChainLengthsDone in *.
    destruct Hlengths as [Hnext Hdone].
    split; [exact Hnext |].
    intros length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0.
    specialize (Hdone length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0).
    rewrite Znth_replace_Znth_Diff.
    + exact Hdone.
    + exact Hcurrent.
    + rewrite PreH15. nia.
    + intro Heq.
      assert (Hright0_range : 0 <= right0 < matrix_count_pre) by lia.
      assert (Hright_range :
          0 <= left + chain_length - 1 < matrix_count_pre) by lia.
      destruct (Z.lt_trichotomy left0 left) as [Hlt | [Heql | Hgt]].
      * assert (left0 * matrix_count_pre + right0 <
                left * matrix_count_pre) by nia.
        nia.
      * subst left0. nia.
      * assert (left * matrix_count_pre + (left + chain_length - 1) <
                left0 * matrix_count_pre) by nia.
        nia.
  - intros left0 right0 Hleft0 Hright0 Hfits0.
    destruct (Z.eq_dec left0 left) as [Heq | Hneq].
    + subst left0.
      assert (right0 = left + chain_length - 1) by lia.
      subst right0.
      rewrite Znth_replace_Znth_Same by exact Hcurrent.
      replace (left + chain_length - 1) with right by lia.
      exact PreH19.
    + assert (Hleft0_old : 0 <= left0 < left) by lia.
      specialize (Hleft left0 right0 Hleft0_old Hright0 Hfits0).
      rewrite Znth_replace_Znth_Diff.
      * exact Hleft.
      * exact Hcurrent.
      * rewrite PreH15. nia.
      * intro Hindices.
        assert (Hright0_range : 0 <= right0 < matrix_count_pre) by lia.
        assert (Hright_range :
            0 <= left + chain_length - 1 < matrix_count_pre) by lia.
        assert (left0 * matrix_count_pre + right0 <
                left * matrix_count_pre) by nia.
        nia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_12_split_goal_2 : matrixChainMinCost_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hcurrent :
      0 <= left * matrix_count_pre + (left + chain_length - 1) <
           Zlength cost_l_2).
  { rewrite PreH15. rewrite <- PreH7. lia. }
  unfold MatrixChainTableValuesBounded in *.
  intros index Hindex.
  rewrite Zlength_replace_Znth in Hindex.
  destruct (Z.eq_dec index
      (left * matrix_count_pre + (left + chain_length - 1))) as [Heq | Hneq].
  - subst index.
    rewrite Znth_replace_Znth_Same by exact Hcurrent.
    lia.
  - rewrite Znth_replace_Znth_Diff.
    + apply PreH17. exact Hindex.
    + exact Hcurrent.
    + exact Hindex.
    + intro Heq. apply Hneq. symmetry. exact Heq.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_12_split_goal_3 : matrixChainMinCost_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH15.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 : matrixChainMinCost_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainLeftProgress in PreH12.
  destruct PreH12 as [Hlengths Hleft].
  unfold MatrixChainLengthsDone in *.
  destruct Hlengths as [Hlengths_lb Hlengths_done].
  split.
  - lia.
  - intros length0 left0 right0 Hlength0 Hright0 Hleft0 Hfits0.
    destruct (Z_lt_ge_dec length0 chain_length) as [Hlt | Hge].
    + eapply Hlengths_done; eauto; lia.
    + assert (length0 = chain_length) by lia.
      subst length0.
      eapply Hleft; eauto; lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_1 : matrixChainMinCost_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hchain : chain_length = matrix_count_pre + 1) by lia.
  unfold MatrixChainMinimumCost.
  split.
  - exact PreH4.
  - unfold MatrixChainLengthsDone in PreH10.
    destruct PreH10 as [_ Hdone].
    eapply Hdone with (length := matrix_count_pre) (left := 0) (right := matrix_count_pre - 1).
    + rewrite Hchain. lia.
    + lia.
    + lia.
    + lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_2 : matrixChainMinCost_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hchain : chain_length = matrix_count_pre + 1) by lia.
  unfold MatrixChainTableResult.
  split.
  - exact PreH5.
  - intros left0 right0 [Hleft0 [Horder Hright0]].
    unfold MatrixChainLengthsDone in PreH10.
    destruct PreH10 as [_ Hdone].
    eapply Hdone with
        (length := right0 - left0 + 1)
        (left := left0) (right := right0).
    + rewrite Hchain. lia.
    + lia.
    + lia.
    + lia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_3 : matrixChainMinCost_entail_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (matrix_count_pre + 1) with chain_length by lia.
  exact PreH10.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_4 : matrixChainMinCost_entail_wit_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH9.
  specialize (PreH9 (matrix_count_pre - 1)).
  rewrite PreH5 in PreH9.
  destruct PreH9 as [_ Hupper]; nia.
Qed.
Lemma proof_of_matrixChainMinCost_entail_wit_14_split_goal_5 : matrixChainMinCost_entail_wit_14_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixChainTableValuesBounded in PreH9.
  specialize (PreH9 (matrix_count_pre - 1)).
  rewrite PreH5 in PreH9.
  destruct PreH9 as [Hlower _]; nia.
Qed.
End ReusedProof.


Lemma matrix_bounds_iff : forall xs lo hi,
  (Forall (Z.le lo) xs /\ Forall (Z.ge hi) xs) <->
  (forall i, 0 <= i < Zlength xs -> lo <= Znth i xs 0 <= hi).
Proof.
  intros xs lo hi. split.
  - intros [Hl Hh] i Hi.
    pose proof (proj1 (Forall_Znth (Z.le lo) 0 xs) Hl i Hi) as H1.
    pose proof (proj1 (Forall_Znth (Z.ge hi) 0 xs) Hh i Hi) as H2.
    apply Z.ge_le in H2. lia.
  - intros H. split.
    + apply (proj2 (Forall_Znth (Z.le lo) 0 xs)). intros i Hi. specialize (H i Hi). lia.
    + apply (proj2 (Forall_Znth (Z.ge hi) 0 xs)). intros i Hi. specialize (H i Hi). apply Z.le_ge. lia.
Qed.
Lemma matrix_dims_iff : forall xs n,
  MatrixChainDimensionsBounded xs n <->
  Zlength xs = n + 1 /\ Forall (Z.le 1) xs /\ Forall (Z.ge 100) xs.
Proof.
  intros xs n. unfold MatrixChainDimensionsBounded. rewrite matrix_bounds_iff.
  split; intros [Hlen H]; (split; [exact Hlen | intros i Hi; apply H; lia]).
Qed.
Lemma matrix_zero_iff : forall xs n,
  MatrixChainZeroPrefix xs n <-> Zlength xs = n /\ Forall (eq 0) xs.
Proof.
  intros xs n. unfold MatrixChainZeroPrefix. rewrite (Forall_Znth (eq 0) 0 xs).
  split; intros [Hlen H]; (split; [exact Hlen | intros i Hi; specialize (H i ltac:(lia)); lia]).
Qed.
Ltac matrix_math :=
  try solve [assumption | reflexivity];
  repeat rewrite matrix_dims_iff in *;
  repeat rewrite matrix_zero_iff in *;
  unfold MatrixChainTableValuesBounded in *;
  repeat rewrite <- (matrix_bounds_iff _ 0 7000000) in *;
  unfold MatrixChainMinimumCost, MatrixChainTableResult, MatrixChainSplitProgress,
    MatrixChainLeftProgress, MatrixChainLengthsDone,
    MatrixChainOptimalCost, MatrixChainTableComplete, MatrixChainSplitMinimum,
    MatrixChainLeftComplete, MatrixChainLengthsComplete in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end];
  try lia;
  repeat match goal with
  | H : Forall ?P ?xs |- _ => rewrite (Forall_Znth P 0 xs) in H
  | |- Forall ?P ?xs => apply (proj2 (Forall_Znth P 0 xs))
  end;
  try solve [assumption | intuition lia];
  try solve [intros; match goal with |- context[Znth ?i ?xs 0] =>
    repeat match goal with H : forall j : Z, _ -> _ |- _ =>
      let K := fresh "AtIndex" in pose proof (H i ltac:(lia)) as K; clear H
    end; lia
  end];
  try nia.






























Lemma scratch_full_tail_undef : forall x k cap l,
  0 <= k <= cap ->
  IntArray.full x k l ** IntArray.undef_seg x k cap |-- IntArray.undef_full x cap.
Proof.
  intros x k cap l Hk.
  sep_apply (IntArray.full_to_undef_full x k l).
  sep_apply (IntArray.undef_full_to_undef_seg x k).
  sep_apply (IntArray.undef_seg_merge_to_undef_full x 0 k cap Hk).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (cap - 0) with cap by lia. entailer!.
Qed.






Lemma proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1.
Proof.
  unfold matrixChainMinCost_entail_wit_1; right; intros.
  assert (LegacyPreH1 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH4 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_1_split_goal_1 matrix_count_pre dimensions_l LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4) as LegacyFact0.
  split_pure_spatial.
  - try (sep_apply (IntArray.undef_full_split_to_undef_seg (&("cost")) (matrix_count_pre * matrix_count_pre) 64 ltac:(nia))); repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2.
Proof.
  unfold matrixChainMinCost_entail_wit_2; right; intros.
  assert (LegacyPreH1 : (i < (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH5 : (0 <= i)) by matrix_math.
  assert (LegacyPreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH8 : (MatrixChainZeroPrefix cost_l_2 i )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_2_split_goal_1 matrix_count_pre dimensions_l cost_l_2 i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8) as LegacyFact0.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3.
Proof.
  unfold matrixChainMinCost_entail_wit_3.
  destruct ReusedProof.proof_of_matrixChainMinCost_entail_wit_3 as [Hfull | Hsegment].
  { left; intros.
  assert (LegacyPreH1 : (i >= (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH5 : (0 <= i)) by matrix_math.
  assert (LegacyPreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH8 : (MatrixChainZeroPrefix cost_l_2 i )) by matrix_math.
  pose proof (Hfull (&("cost")) matrix_count_pre dimensions_pre dimensions_l cost_l_2 i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8) as Hreused.
  sep_apply Hreused.
  Intros cost_l_reused.
  Exists cost_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
  }
  { right; intros.
  assert (LegacyPreH1 : (i >= (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH5 : (0 <= i)) by matrix_math.
  assert (LegacyPreH6 : (i <= (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH7 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH8 : (MatrixChainZeroPrefix cost_l_2 i )) by matrix_math.
  pose proof (Hsegment (&("cost")) matrix_count_pre dimensions_l cost_l_2 i LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8) as Hreused.
  sep_apply Hreused.
  Intros cost_l_reused.
  Exists cost_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
  }
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_4 : matrixChainMinCost_entail_wit_4.
Proof.
  unfold matrixChainMinCost_entail_wit_4; right; intros.
  assert (LegacyPreH1 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH6 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH7 : (chain_length <= (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH9 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH10 : (MatrixChainLengthsDone dimensions_l cost_l_2 matrix_count_pre chain_length )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_5_split_goal_1 matrix_count_pre dimensions_l chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10) as LegacyFact0.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5.
Proof.
  unfold matrixChainMinCost_entail_wit_5; right; intros.
  assert (LegacyPreH1 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH6 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH7 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH8 : (0 <= left)) by matrix_math.
  assert (LegacyPreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) by matrix_math.
  assert (LegacyPreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH11 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_1 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact0.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_2 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact1.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_3 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact2.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_4 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact3.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_5 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact4.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_6 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact5.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_7 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact6.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_8 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact7.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_9 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact8.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_10 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact9.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_11 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact10.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_6_split_goal_12 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact11.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6.
Proof.
  unfold matrixChainMinCost_entail_wit_6; right; intros.
  assert (LegacyPreH1 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH3 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH4 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH5 : (0 <= left)) by matrix_math.
  assert (LegacyPreH6 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH7 : (right = ((left + chain_length ) - 1 ))) by matrix_math.
  assert (LegacyPreH8 : (left < right)) by matrix_math.
  assert (LegacyPreH9 : (right < matrix_count_pre)) by matrix_math.
  assert (LegacyPreH10 : (0 <= ((left * matrix_count_pre ) + left ))) by matrix_math.
  assert (LegacyPreH11 : (((left * matrix_count_pre ) + left ) < (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH12 : (0 <= (((left + 1 ) * matrix_count_pre ) + right ))) by matrix_math.
  assert (LegacyPreH13 : ((((left + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH14 : (0 <= left)) by matrix_math.
  assert (LegacyPreH15 : (left < (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH16 : (0 <= (left + 1 ))) by matrix_math.
  assert (LegacyPreH17 : ((left + 1 ) < (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH18 : (0 <= (right + 1 ))) by matrix_math.
  assert (LegacyPreH19 : ((right + 1 ) < (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH22 : (0 <= (Znth ((left * matrix_count_pre ) + left ) cost_l 0))) by matrix_math.
  assert (LegacyPreH23 : ((Znth ((left * matrix_count_pre ) + left ) cost_l 0) <= 7000000)) by matrix_math.
  assert (LegacyPreH24 : (0 <= (Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0))) by matrix_math.
  assert (LegacyPreH25 : ((Znth (((left + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) by matrix_math.
  assert (LegacyPreH26 : (1 <= (Znth left dimensions_l 0))) by matrix_math.
  assert (LegacyPreH27 : ((Znth left dimensions_l 0) <= 100)) by matrix_math.
  assert (LegacyPreH28 : (1 <= (Znth (left + 1 ) dimensions_l 0))) by matrix_math.
  assert (LegacyPreH29 : ((Znth (left + 1 ) dimensions_l 0) <= 100)) by matrix_math.
  assert (LegacyPreH30 : (1 <= (Znth (right + 1 ) dimensions_l 0))) by matrix_math.
  assert (LegacyPreH31 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) by matrix_math.
  assert (LegacyPreH32 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH33 : (MatrixChainTableValuesBounded cost_l )) by matrix_math.
  assert (LegacyPreH34 : (MatrixChainLeftProgress dimensions_l cost_l matrix_count_pre chain_length left )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_7_split_goal_1 matrix_count_pre dimensions_l cost_l chain_length left right LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29 LegacyPreH30 LegacyPreH31 LegacyPreH32 LegacyPreH33 LegacyPreH34) as LegacyFact0.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_7_split_goal_2 matrix_count_pre dimensions_l cost_l chain_length left right LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29 LegacyPreH30 LegacyPreH31 LegacyPreH32 LegacyPreH33 LegacyPreH34) as LegacyFact1.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7.
Proof.
  unfold matrixChainMinCost_entail_wit_7; right; intros.
  assert (LegacyPreH1 : (split < right)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH5 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH6 : (0 <= left)) by matrix_math.
  assert (LegacyPreH7 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH8 : (right = ((left + chain_length ) - 1 ))) by matrix_math.
  assert (LegacyPreH9 : (left < right)) by matrix_math.
  assert (LegacyPreH10 : (right < matrix_count_pre)) by matrix_math.
  assert (LegacyPreH11 : ((left + 1 ) <= split)) by matrix_math.
  assert (LegacyPreH12 : (split <= right)) by matrix_math.
  assert (LegacyPreH13 : (0 <= best)) by matrix_math.
  assert (LegacyPreH14 : (best <= 7000000)) by matrix_math.
  assert (LegacyPreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH18 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_1 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact0.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_2 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact1.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_3 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact2.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_4 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact3.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_5 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact4.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_6 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact5.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_7 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact6.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_8 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact7.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_9 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact8.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_10 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact9.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_11 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact10.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_8_split_goal_12 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact11.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8.
Proof.
  unfold matrixChainMinCost_entail_wit_8; right; intros.
  assert (LegacyPreH1 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH3 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH4 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH5 : (0 <= left)) by matrix_math.
  assert (LegacyPreH6 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH7 : (right = ((left + chain_length ) - 1 ))) by matrix_math.
  assert (LegacyPreH8 : (left < right)) by matrix_math.
  assert (LegacyPreH9 : (right < matrix_count_pre)) by matrix_math.
  assert (LegacyPreH10 : ((left + 1 ) <= split)) by matrix_math.
  assert (LegacyPreH11 : (split < right)) by matrix_math.
  assert (LegacyPreH12 : (0 <= ((left * matrix_count_pre ) + split ))) by matrix_math.
  assert (LegacyPreH13 : (((left * matrix_count_pre ) + split ) < (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH14 : (0 <= (((split + 1 ) * matrix_count_pre ) + right ))) by matrix_math.
  assert (LegacyPreH15 : ((((split + 1 ) * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH16 : (0 <= left)) by matrix_math.
  assert (LegacyPreH17 : (left < (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH18 : (0 <= (split + 1 ))) by matrix_math.
  assert (LegacyPreH19 : ((split + 1 ) < (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH20 : (0 <= (right + 1 ))) by matrix_math.
  assert (LegacyPreH21 : ((right + 1 ) < (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH22 : (0 <= best)) by matrix_math.
  assert (LegacyPreH23 : (best <= 7000000)) by matrix_math.
  assert (LegacyPreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH26 : (0 <= (Znth ((left * matrix_count_pre ) + split ) cost_l 0))) by matrix_math.
  assert (LegacyPreH27 : ((Znth ((left * matrix_count_pre ) + split ) cost_l 0) <= 7000000)) by matrix_math.
  assert (LegacyPreH28 : (0 <= (Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0))) by matrix_math.
  assert (LegacyPreH29 : ((Znth (((split + 1 ) * matrix_count_pre ) + right ) cost_l 0) <= 7000000)) by matrix_math.
  assert (LegacyPreH30 : (1 <= (Znth left dimensions_l 0))) by matrix_math.
  assert (LegacyPreH31 : ((Znth left dimensions_l 0) <= 100)) by matrix_math.
  assert (LegacyPreH32 : (1 <= (Znth (split + 1 ) dimensions_l 0))) by matrix_math.
  assert (LegacyPreH33 : ((Znth (split + 1 ) dimensions_l 0) <= 100)) by matrix_math.
  assert (LegacyPreH34 : (1 <= (Znth (right + 1 ) dimensions_l 0))) by matrix_math.
  assert (LegacyPreH35 : ((Znth (right + 1 ) dimensions_l 0) <= 100)) by matrix_math.
  assert (LegacyPreH36 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH37 : (MatrixChainTableValuesBounded cost_l )) by matrix_math.
  assert (LegacyPreH38 : (MatrixChainSplitProgress dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_9_split_goal_1 matrix_count_pre dimensions_l cost_l chain_length left right split best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29 LegacyPreH30 LegacyPreH31 LegacyPreH32 LegacyPreH33 LegacyPreH34 LegacyPreH35 LegacyPreH36 LegacyPreH37 LegacyPreH38) as LegacyFact0.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_9_split_goal_2 matrix_count_pre dimensions_l cost_l chain_length left right split best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29 LegacyPreH30 LegacyPreH31 LegacyPreH32 LegacyPreH33 LegacyPreH34 LegacyPreH35 LegacyPreH36 LegacyPreH37 LegacyPreH38) as LegacyFact1.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_9_1 : matrixChainMinCost_entail_wit_9_1.
Proof.
  unfold matrixChainMinCost_entail_wit_9_1; right; intros.
  assert (LegacyPreH1 : (candidate < best)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH5 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH6 : (0 <= left)) by matrix_math.
  assert (LegacyPreH7 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH8 : (right = ((left + chain_length ) - 1 ))) by matrix_math.
  assert (LegacyPreH9 : (left < right)) by matrix_math.
  assert (LegacyPreH10 : (right < matrix_count_pre)) by matrix_math.
  assert (LegacyPreH11 : ((left + 1 ) <= split)) by matrix_math.
  assert (LegacyPreH12 : (split < right)) by matrix_math.
  assert (LegacyPreH13 : (0 <= best)) by matrix_math.
  assert (LegacyPreH14 : (best <= 7000000)) by matrix_math.
  assert (LegacyPreH15 : (0 <= candidate)) by matrix_math.
  assert (LegacyPreH16 : (candidate <= 7000000)) by matrix_math.
  assert (LegacyPreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH20 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) by matrix_math.
  assert (LegacyPreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_10_1_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22) as LegacyFact0.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_9_2 : matrixChainMinCost_entail_wit_9_2.
Proof.
  unfold matrixChainMinCost_entail_wit_9_2; right; intros.
  assert (LegacyPreH1 : (candidate >= best)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH5 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH6 : (0 <= left)) by matrix_math.
  assert (LegacyPreH7 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH8 : (right = ((left + chain_length ) - 1 ))) by matrix_math.
  assert (LegacyPreH9 : (left < right)) by matrix_math.
  assert (LegacyPreH10 : (right < matrix_count_pre)) by matrix_math.
  assert (LegacyPreH11 : ((left + 1 ) <= split)) by matrix_math.
  assert (LegacyPreH12 : (split < right)) by matrix_math.
  assert (LegacyPreH13 : (0 <= best)) by matrix_math.
  assert (LegacyPreH14 : (best <= 7000000)) by matrix_math.
  assert (LegacyPreH15 : (0 <= candidate)) by matrix_math.
  assert (LegacyPreH16 : (candidate <= 7000000)) by matrix_math.
  assert (LegacyPreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH19 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH20 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH21 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate )) by matrix_math.
  assert (LegacyPreH22 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_10_2_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right split best candidate LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22) as LegacyFact0.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_10 : matrixChainMinCost_entail_wit_10.
Proof.
  unfold matrixChainMinCost_entail_wit_10; right; intros.
  assert (LegacyPreH1 : (split >= right)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH5 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH6 : (0 <= left)) by matrix_math.
  assert (LegacyPreH7 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH8 : (right = ((left + chain_length ) - 1 ))) by matrix_math.
  assert (LegacyPreH9 : (left < right)) by matrix_math.
  assert (LegacyPreH10 : (right < matrix_count_pre)) by matrix_math.
  assert (LegacyPreH11 : ((left + 1 ) <= split)) by matrix_math.
  assert (LegacyPreH12 : (split <= right)) by matrix_math.
  assert (LegacyPreH13 : (0 <= best)) by matrix_math.
  assert (LegacyPreH14 : (best <= 7000000)) by matrix_math.
  assert (LegacyPreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH17 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH18 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH19 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_11_split_goal_1 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact0.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_11_split_goal_2 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact1.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_11_split_goal_3 matrix_count_pre dimensions_l cost_l_2 best split right left chain_length LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11.
Proof.
  unfold matrixChainMinCost_entail_wit_11; right; intros.
  assert (LegacyPreH1 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH3 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH4 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH5 : (0 <= left)) by matrix_math.
  assert (LegacyPreH6 : ((left + chain_length ) <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH7 : (right = ((left + chain_length ) - 1 ))) by matrix_math.
  assert (LegacyPreH8 : (left < right)) by matrix_math.
  assert (LegacyPreH9 : (right < matrix_count_pre)) by matrix_math.
  assert (LegacyPreH10 : (0 <= best)) by matrix_math.
  assert (LegacyPreH11 : (best <= 7000000)) by matrix_math.
  assert (LegacyPreH12 : (0 <= ((left * matrix_count_pre ) + right ))) by matrix_math.
  assert (LegacyPreH13 : (((left * matrix_count_pre ) + right ) < (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH16 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH17 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH18 : (MatrixChainSplitProgress dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best )) by matrix_math.
  assert (LegacyPreH19 : (MatrixChainIntervalMinimum dimensions_l left right best )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_12_split_goal_1 matrix_count_pre dimensions_l cost_l_2 chain_length left right best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact0.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_12_split_goal_2 matrix_count_pre dimensions_l cost_l_2 chain_length left right best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact1.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_12_split_goal_3 matrix_count_pre dimensions_l cost_l_2 chain_length left right best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19) as LegacyFact2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12.
Proof.
  unfold matrixChainMinCost_entail_wit_12; right; intros.
  assert (LegacyPreH1 : ((left + chain_length ) > matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH6 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH7 : (chain_length <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH8 : (0 <= left)) by matrix_math.
  assert (LegacyPreH9 : (left <= ((matrix_count_pre - chain_length ) + 1 ))) by matrix_math.
  assert (LegacyPreH10 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH11 : (MatrixChainTableValuesBounded cost_l_2 )) by matrix_math.
  assert (LegacyPreH12 : (MatrixChainLeftProgress dimensions_l cost_l_2 matrix_count_pre chain_length left )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_13_split_goal_1 matrix_count_pre dimensions_l left chain_length cost_l_2 LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12) as LegacyFact0.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.

Lemma proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13.
Proof.
  unfold matrixChainMinCost_entail_wit_13; right; intros.
  assert (LegacyPreH1 : (chain_length > matrix_count_pre)) by matrix_math.
  assert (LegacyPreH2 : (1 <= matrix_count_pre)) by matrix_math.
  assert (LegacyPreH3 : (matrix_count_pre <= 8)) by matrix_math.
  assert (LegacyPreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre ))) by matrix_math.
  assert (LegacyPreH6 : (2 <= chain_length)) by matrix_math.
  assert (LegacyPreH7 : (chain_length <= (matrix_count_pre + 1 ))) by matrix_math.
  assert (LegacyPreH8 : (MatrixChainDimensionsBounded dimensions_l matrix_count_pre )) by matrix_math.
  assert (LegacyPreH9 : (MatrixChainTableValuesBounded cost_l )) by matrix_math.
  assert (LegacyPreH10 : (MatrixChainLengthsDone dimensions_l cost_l matrix_count_pre chain_length )) by matrix_math.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_14_split_goal_1 matrix_count_pre dimensions_l chain_length cost_l LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10) as LegacyFact0.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_14_split_goal_2 matrix_count_pre dimensions_l chain_length cost_l LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10) as LegacyFact1.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_14_split_goal_3 matrix_count_pre dimensions_l chain_length cost_l LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10) as LegacyFact2.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_14_split_goal_4 matrix_count_pre dimensions_l chain_length cost_l LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10) as LegacyFact3.
  pose proof (ReusedProof.proof_of_matrixChainMinCost_entail_wit_14_split_goal_5 matrix_count_pre dimensions_l chain_length cost_l LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10) as LegacyFact4.
  split_pure_spatial.
  - apply scratch_full_tail_undef. nia.
  - split_pures; dump_pre_spatial; matrix_math.
Qed.
