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
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P010_412A_poster_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_proof.

(*----- Function write_left -----*)

Definition write_left_safety_wit_1 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full dst_pre 8 before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_left_safety_wit_2 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full dst_pre 8 before )
|--
  “ (76 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 76) ”
.

Definition write_left_safety_wit_3 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (76) (before)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition write_left_safety_wit_4 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (76) (before)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition write_left_safety_wit_5 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition write_left_safety_wit_6 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (70 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 70) ”
.

Definition write_left_safety_wit_7 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition write_left_safety_wit_8 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (84 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 84) ”
.

Definition write_left_safety_wit_9 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition write_left_safety_wit_10 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_left_return_wit_1 := 
(
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (4) (0) ((replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))))) )
|--
  EX (after: (@list Z)) ,
  “ ((Zlength (after)) = 8) ” 
  &&  “ (ActionSlotBridge LeftAction before after ) ”
  &&  (CharArray.full dst_pre 8 after )
) \/
(
forall (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  TT && emp 
|--
  “ (ActionSlotBridge LeftAction before (replace_Znth (4) (0) ((replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (4) (0) ((replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))))))) = 8) ”
  &&  emp
).

Definition write_left_return_wit_1_split_goal_1 := 
forall (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (ActionSlotBridge LeftAction before (replace_Znth (4) (0) ((replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))))) )
.

Definition write_left_return_wit_1_split_goal_2 := 
forall (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  ((Zlength ((replace_Znth (4) (0) ((replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))))))) = 8)
.

Definition write_left_partial_solve_wit_1 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 before )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 0 0 8 before )
.

Definition write_left_partial_solve_wit_2 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (76) (before)) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (1 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 1 0 8 (replace_Znth (0) (76) (before)) )
.

Definition write_left_partial_solve_wit_3 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (2 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 2 0 8 (replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))) )
.

Definition write_left_partial_solve_wit_4 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (3 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 3 0 8 (replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))) )
.

Definition write_left_partial_solve_wit_5 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (4 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 4 0 8 (replace_Znth (3) (84) ((replace_Znth (2) (70) ((replace_Znth (1) (69) ((replace_Znth (0) (76) (before)))))))) )
.

(*----- Function write_right -----*)

Definition write_right_safety_wit_1 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full dst_pre 8 before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_right_safety_wit_2 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  (CharArray.full dst_pre 8 before )
|--
  “ (82 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 82) ”
.

Definition write_right_safety_wit_3 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (82) (before)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition write_right_safety_wit_4 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (82) (before)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition write_right_safety_wit_5 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition write_right_safety_wit_6 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (71 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 71) ”
.

Definition write_right_safety_wit_7 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition write_right_safety_wit_8 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (72 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 72) ”
.

Definition write_right_safety_wit_9 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition write_right_safety_wit_10 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (84 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 84) ”
.

Definition write_right_safety_wit_11 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition write_right_safety_wit_12 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_right_return_wit_1 := 
(
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (5) (0) ((replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))))) )
|--
  EX (after: (@list Z)) ,
  “ ((Zlength (after)) = 8) ” 
  &&  “ (ActionSlotBridge RightAction before after ) ”
  &&  (CharArray.full dst_pre 8 after )
) \/
(
forall (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  TT && emp 
|--
  “ (ActionSlotBridge RightAction before (replace_Znth (5) (0) ((replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (5) (0) ((replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))))))) = 8) ”
  &&  emp
).

Definition write_right_return_wit_1_split_goal_1 := 
forall (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (ActionSlotBridge RightAction before (replace_Znth (5) (0) ((replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))))) )
.

Definition write_right_return_wit_1_split_goal_2 := 
forall (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  ((Zlength ((replace_Znth (5) (0) ((replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))))))) = 8)
.

Definition write_right_partial_solve_wit_1 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 before )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 0 0 8 before )
.

Definition write_right_partial_solve_wit_2 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (82) (before)) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (1 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 1 0 8 (replace_Znth (0) (82) (before)) )
.

Definition write_right_partial_solve_wit_3 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (2 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 2 0 8 (replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))) )
.

Definition write_right_partial_solve_wit_4 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (3 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 3 0 8 (replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))) )
.

Definition write_right_partial_solve_wit_5 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (4 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 4 0 8 (replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))) )
.

Definition write_right_partial_solve_wit_6 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (5 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 5 0 8 (replace_Znth (4) (84) ((replace_Znth (3) (72) ((replace_Znth (2) (71) ((replace_Znth (1) (73) ((replace_Znth (0) (82) (before)))))))))) )
.

(*----- Function write_print -----*)

Definition write_print_safety_wit_1 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
  **  (CharArray.full dst_pre 8 before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_print_safety_wit_2 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
  **  (CharArray.full dst_pre 8 before )
|--
  “ (80 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 80) ”
.

Definition write_print_safety_wit_3 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (80) (before)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition write_print_safety_wit_4 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (80) (before)) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (82 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 82) ”
.

Definition write_print_safety_wit_5 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition write_print_safety_wit_6 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition write_print_safety_wit_7 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition write_print_safety_wit_8 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (78 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 78) ”
.

Definition write_print_safety_wit_9 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition write_print_safety_wit_10 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (84 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 84) ”
.

Definition write_print_safety_wit_11 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition write_print_safety_wit_12 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition write_print_safety_wit_13 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition write_print_safety_wit_14 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition write_print_safety_wit_15 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))) )
  **  ((( &( "dst" ) )) # Ptr  |-> dst_pre)
  **  ((( &( "ch" ) )) # Char  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition write_print_return_wit_1 := 
(
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (7) (0) ((replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))))) )
|--
  EX (after: (@list Z)) ,
  “ ((Zlength (after)) = 8) ” 
  &&  “ (ActionSlotBridge (PrintAction (ch_pre)) before after ) ”
  &&  (CharArray.full dst_pre 8 after )
) \/
(
forall (ch_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  TT && emp 
|--
  “ (ActionSlotBridge (PrintAction (ch_pre)) before (replace_Znth (7) (0) ((replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (7) (0) ((replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))))))) = 8) ”
  &&  emp
).

Definition write_print_return_wit_1_split_goal_1 := 
forall (ch_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (ActionSlotBridge (PrintAction (ch_pre)) before (replace_Znth (7) (0) ((replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))))) )
.

Definition write_print_return_wit_1_split_goal_2 := 
forall (ch_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  ((Zlength ((replace_Znth (7) (0) ((replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))))))) = 8)
.

Definition write_print_partial_solve_wit_1 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 before )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 0 0 8 before )
.

Definition write_print_partial_solve_wit_2 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (0) (80) (before)) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (1 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 1 0 8 (replace_Znth (0) (80) (before)) )
.

Definition write_print_partial_solve_wit_3 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (2 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 2 0 8 (replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))) )
.

Definition write_print_partial_solve_wit_4 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (3 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 3 0 8 (replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))) )
.

Definition write_print_partial_solve_wit_5 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (4 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 4 0 8 (replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))) )
.

Definition write_print_partial_solve_wit_6 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (5 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 5 0 8 (replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))) )
.

Definition write_print_partial_solve_wit_7 := 
forall (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (6 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 6 0 8 (replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))) )
.

Definition write_print_partial_solve_wit_8 := 
forall (ch_pre: Z) (dst_pre: Z) (before: (@list Z)) (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (before)) = 8)) ,
  (CharArray.full dst_pre 8 (replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))) )
|--
  “ (0 <= 8) ” 
  &&  “ ((Zlength (before)) = 8) ”
  &&  (((dst_pre + (7 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i dst_pre 7 0 8 (replace_Znth (6) (ch_pre) ((replace_Znth (5) (32) ((replace_Znth (4) (84) ((replace_Znth (3) (78) ((replace_Znth (2) (73) ((replace_Znth (1) (82) ((replace_Znth (0) (80) (before)))))))))))))) )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((((((65 <= (Znth i text 0)) /\ ((Znth i text 0) <= 90)) \/ ((48 <= (Znth i text 0)) /\ ((Znth i text 0) <= 57))) \/ ((Znth i text 0) = 46)) \/ ((Znth i text 0) = 33)) \/ ((Znth i text 0) = 44)) \/ ((Znth i text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 out_before __default__List_Z))) = 8))) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_before )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((((((65 <= (Znth i text 0)) /\ ((Znth i text 0) <= 90)) \/ ((48 <= (Znth i text 0)) /\ ((Znth i text 0) <= 57))) \/ ((Znth i text 0) = 46)) \/ ((Znth i text 0) = 33)) \/ ((Znth i text 0) = 44)) \/ ((Znth i text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 out_before __default__List_Z))) = 8))) ,
  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_before )
|--
  “ ((n_pre - k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - k_pre )) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((((((65 <= (Znth i text 0)) /\ ((Znth i text 0) <= 90)) \/ ((48 <= (Znth i text 0)) /\ ((Znth i text 0) <= 57))) \/ ((Znth i text 0) = 46)) \/ ((Znth i text 0) = 33)) \/ ((Znth i text 0) = 44)) \/ ((Znth i text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 out_before __default__List_Z))) = 8))) ,
  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_before )
|--
  “ ((k_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k_pre - 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((((((65 <= (Znth i text 0)) /\ ((Znth i text 0) <= 90)) \/ ((48 <= (Znth i text 0)) /\ ((Znth i text 0) <= 57))) \/ ((Znth i text 0) = 46)) \/ ((Znth i text 0) = 33)) \/ ((Znth i text 0) = 44)) \/ ((Znth i text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH9 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 out_before __default__List_Z))) = 8))) ,
  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_before )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH10 : (1 <= p)) (PreH11 : (p <= k_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH15 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH16 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows )) (PreH17 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH10 : (1 < p)) (PreH11 : (p <= k_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH18 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge LeftAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH12 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH13 : (1 < p)) (PreH14 : (p <= k_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH21 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge LeftAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH12 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH13 : (1 < p)) (PreH14 : (p <= k_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH21 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> (t + 1 ))
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((p - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p - 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows )) (PreH18 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((p - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p - 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= 8)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH10 : (n_pre = (Zlength (text)))) (PreH11 : (k_pre = cursor)) (PreH12 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH13 : (1 <= p)) (PreH14 : (p <= n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH20 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH21 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH22 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH23 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH24 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH25 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p < n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH17 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH18 : (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge RightAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH12 : (1 <= p)) (PreH13 : (p < n_pre)) (PreH14 : (0 <= t)) (PreH15 : (t < (3 * n_pre ))) (PreH16 : (0 <= (t + 1 ))) (PreH17 : ((t + 1 ) < (3 * n_pre ))) (PreH18 : ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre ))) (PreH19 : (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH20 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH21 : (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge RightAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH12 : (1 <= p)) (PreH13 : (p < n_pre)) (PreH14 : (0 <= t)) (PreH15 : (t < (3 * n_pre ))) (PreH16 : (0 <= (t + 1 ))) (PreH17 : ((t + 1 ) < (3 * n_pre ))) (PreH18 : ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre ))) (PreH19 : (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH20 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH21 : (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> (t + 1 ))
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH25 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> (t + 1 ))
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH10 : (k_pre <= p)) (PreH11 : (p < n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH18 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge RightAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH12 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH13 : (k_pre <= p)) (PreH14 : (p < n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH21 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition solver_safety_wit_20 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge RightAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH12 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH13 : (k_pre <= p)) (PreH14 : (p < n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH21 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> (t + 1 ))
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((p + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p + 1 )) ”
.

Definition solver_safety_wit_21 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (0 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : ((p > 0) -> ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )))) (PreH14 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH15 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH16 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH17 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((p - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p - 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_25 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= 8)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH10 : (n_pre = (Zlength (text)))) (PreH11 : (k_pre = cursor)) (PreH12 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH13 : (1 <= p)) (PreH14 : (p <= n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH20 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH21 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH22 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH23 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH24 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH25 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition solver_safety_wit_26 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= 8)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH10 : (n_pre = (Zlength (text)))) (PreH11 : (k_pre = cursor)) (PreH12 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH13 : (1 <= p)) (PreH14 : (p <= n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH20 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH21 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH22 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH23 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH24 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH25 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> (t + 1 ))
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (1 < p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((t + (2 * (p - 1 ) ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH17 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH18 : (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_28 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge LeftAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH12 : (1 < p)) (PreH13 : (p <= n_pre)) (PreH14 : (0 <= t)) (PreH15 : (t < (3 * n_pre ))) (PreH16 : (0 <= (t + 1 ))) (PreH17 : ((t + 1 ) < (3 * n_pre ))) (PreH18 : ((t + (2 * (p - 1 ) ) ) < (3 * n_pre ))) (PreH19 : (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH20 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH21 : (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge LeftAction (Znth t rows __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH12 : (1 < p)) (PreH13 : (p <= n_pre)) (PreH14 : (0 <= t)) (PreH15 : (t < (3 * n_pre ))) (PreH16 : (0 <= (t + 1 ))) (PreH17 : ((t + 1 ) < (3 * n_pre ))) (PreH18 : ((t + (2 * (p - 1 ) ) ) < (3 * n_pre ))) (PreH19 : (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH20 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH21 : (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH22 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> (t + 1 ))
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((p - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p - 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH25 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> (t + 1 ))
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
|--
  “ ((p - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p - 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_before )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= k_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (3 * n_pre )) ” 
  &&  “ (((0 + (k_pre - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (0 = (Zlength ((LeftWalkPlan (k_pre) (k_pre))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (k_pre)) 0 out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  TT && emp 
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i out_before __default__List_Z))) = 8)) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (k_pre)) 0 out_before out_before ) ” 
  &&  “ (0 = (Zlength ((LeftWalkPlan (k_pre) (k_pre))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i out_before __default__List_Z))) = 8))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (k_pre)) 0 out_before out_before )
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (0 = (Zlength ((LeftWalkPlan (k_pre) (k_pre)))))
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )
.

Definition solver_entail_wit_1_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p > 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (1 < p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((LeftWalkPlan (k_pre) (p))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p > 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (1 < p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((LeftWalkPlan (k_pre) (p))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
).

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge LeftAction (Znth t rows_2 __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH12 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH13 : (1 < p)) (PreH14 : (p <= k_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH21 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH22 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (1 <= (p - 1 )) ” 
  &&  “ ((p - 1 ) <= k_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((((t + 1 ) + ((p - 1 ) - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((LeftWalkPlan (k_pre) ((p - 1 )))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) ((p - 1 ))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge LeftAction (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH10 : (n_pre = (Zlength (text)))) (PreH11 : (k_pre = cursor)) (PreH12 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH13 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH14 : (1 < p)) (PreH15 : (p <= k_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH21 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH22 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH23 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH24 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (1 <= (p - 1 )) ” 
  &&  “ ((p - 1 ) <= k_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((((t + 1 ) + ((p - 1 ) - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((LeftWalkPlan (k_pre) ((p - 1 )))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) ((p - 1 ))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
).

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ ((1 <= n_pre) -> ((t + ((2 * (n_pre - 1 ) ) + 1 ) ) < (3 * n_pre ))) ” 
  &&  “ (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (1))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (1)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  TT && emp 
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows_2 __default__List_Z))) = 8)) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (1)))) t out_before rows_2 ) ” 
  &&  “ (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (1))))))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows_2 __default__List_Z))) = 8))
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (1)))) t out_before rows_2 )
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (1)))))))
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH11 : (1 <= p)) (PreH12 : (p <= k_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))
.

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= (n_pre + 1 ))) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p <= n_pre) -> ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p <= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= (n_pre + 1 ))) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p <= n_pre) -> ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
).

Definition solver_entail_wit_6 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p < n_pre)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (0 <= ((t + 1 ) + 1 )) ” 
  &&  “ (((t + 1 ) + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + 1 ) + (2 * (n_pre - p ) ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z))))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth (t + 1 ) rows __default__List_Z))) = 8) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre (t + 1 ) 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + ((t + 1 ) * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth (t + 1 ) rows __default__List_Z) )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p < n_pre)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (0 <= ((t + 1 ) + 1 )) ” 
  &&  “ (((t + 1 ) + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + 1 ) + (2 * (n_pre - p ) ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z))))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth (t + 1 ) rows __default__List_Z))) = 8) ”
  &&  (CharArray2.missing_i out_pre (t + 1 ) 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + ((t + 1 ) * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth (t + 1 ) rows __default__List_Z) )
).

Definition solver_entail_wit_7_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge RightAction (Znth t rows_2 __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH12 : (1 <= p)) (PreH13 : (p < n_pre)) (PreH14 : (0 <= t)) (PreH15 : (t < (3 * n_pre ))) (PreH16 : (0 <= (t + 1 ))) (PreH17 : ((t + 1 ) < (3 * n_pre ))) (PreH18 : ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre ))) (PreH19 : (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH20 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH21 : (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows_2 )) (PreH22 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p + 1 ) <= n_pre) -> (((t + 1 ) + ((2 * (n_pre - (p + 1 ) ) ) + 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 )))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge RightAction (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH10 : (n_pre = (Zlength (text)))) (PreH11 : (k_pre = cursor)) (PreH12 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH13 : (1 <= p)) (PreH14 : (p < n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH21 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH22 : (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows_2 )) (PreH23 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH24 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p + 1 ) <= n_pre) -> (((t + 1 ) + ((2 * (n_pre - (p + 1 ) ) ) + 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 )))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
).

Definition solver_entail_wit_7_2 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p + 1 ) <= n_pre) -> (((t + 1 ) + ((2 * (n_pre - (p + 1 ) ) ) + 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 )))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p + 1 ) <= n_pre) -> (((t + 1 ) + ((2 * (n_pre - (p + 1 ) ) ) + 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 )))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) ((p + 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
).

Definition solver_entail_wit_8 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_before )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (k_pre <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (3 * n_pre )) ” 
  &&  “ (((0 + (n_pre - k_pre ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (0 = (Zlength ((RightWalkPlan (k_pre) (k_pre))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (k_pre)) 0 out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  TT && emp 
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i out_before __default__List_Z))) = 8)) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (k_pre)) 0 out_before out_before ) ” 
  &&  “ (0 = (Zlength ((RightWalkPlan (k_pre) (k_pre))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i out_before __default__List_Z))) = 8))
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (k_pre)) 0 out_before out_before )
.

Definition solver_entail_wit_8_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (0 = (Zlength ((RightWalkPlan (k_pre) (k_pre)))))
.

Definition solver_entail_wit_8_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  (Spec k_pre text (RightFirstPlan (k_pre) (text)) )
.

Definition solver_entail_wit_8_split_goal_5 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z)  __default__List_Z (PreH1 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> (((((((65 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 90)) \/ ((48 <= (Znth i_2 text 0)) /\ ((Znth i_2 text 0) <= 57))) \/ ((Znth i_2 text 0) = 46)) \/ ((Znth i_2 text 0) = 33)) \/ ((Znth i_2 text 0) = 44)) \/ ((Znth i_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((Zlength (out_before)) = (3 * n_pre ))) (PreH10 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < (3 * n_pre ))) -> ((Zlength ((Znth i_3 out_before __default__List_Z))) = 8))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))
.

Definition solver_entail_wit_9 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (k_pre <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((RightWalkPlan (k_pre) (p))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (k_pre <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((RightWalkPlan (k_pre) (p))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
).

Definition solver_entail_wit_10 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge RightAction (Znth t rows_2 __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH12 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH13 : (k_pre <= p)) (PreH14 : (p < n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH21 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH22 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (k_pre <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((((t + 1 ) + (n_pre - (p + 1 ) ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((RightWalkPlan (k_pre) ((p + 1 )))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) ((p + 1 ))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge RightAction (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH10 : (n_pre = (Zlength (text)))) (PreH11 : (k_pre = cursor)) (PreH12 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH13 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH14 : (k_pre <= p)) (PreH15 : (p < n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH21 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH22 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH23 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH24 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (k_pre <= (p + 1 )) ” 
  &&  “ ((p + 1 ) <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((((t + 1 ) + (n_pre - (p + 1 ) ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((RightWalkPlan (k_pre) ((p + 1 )))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) ((p + 1 ))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
).

Definition solver_entail_wit_11 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ ((n_pre > 0) -> ((t + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) ” 
  &&  “ (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (n_pre))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (n_pre)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  TT && emp 
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows_2 __default__List_Z))) = 8)) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (n_pre)))) t out_before rows_2 ) ” 
  &&  “ (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (n_pre))))))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows_2 __default__List_Z))) = 8))
.

Definition solver_entail_wit_11_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (n_pre)))) t out_before rows_2 )
.

Definition solver_entail_wit_11_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (n_pre)))))))
.

Definition solver_entail_wit_11_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH11 : (k_pre <= p)) (PreH12 : (p <= n_pre)) (PreH13 : (0 <= t)) (PreH14 : (t < (3 * n_pre ))) (PreH15 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH17 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))
.

Definition solver_entail_wit_12 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (0 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p > 0) -> ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p >= 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (0 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p > 0) -> ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) ,
  (CharArray2.full out_pre (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
).

Definition solver_entail_wit_13 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p > 1)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (1 < p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (0 <= ((t + 1 ) + 1 )) ” 
  &&  “ (((t + 1 ) + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + 1 ) + (2 * (p - 1 ) ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z))))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth (t + 1 ) rows __default__List_Z))) = 8) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre (t + 1 ) 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + ((t + 1 ) * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth (t + 1 ) rows __default__List_Z) )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p > 1)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (1 < p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (0 <= ((t + 1 ) + 1 )) ” 
  &&  “ (((t + 1 ) + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + 1 ) + (2 * (p - 1 ) ) ) < (3 * n_pre )) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z))))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth (t + 1 ) rows __default__List_Z))) = 8) ”
  &&  (CharArray2.missing_i out_pre (t + 1 ) 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + ((t + 1 ) * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth (t + 1 ) rows __default__List_Z) )
).

Definition solver_entail_wit_14_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : ((Zlength (after)) = 8)) (PreH2 : (ActionSlotBridge LeftAction (Znth t rows_2 __default__List_Z) after )) (PreH3 : (0 <= n_pre)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 100)) (PreH8 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH9 : (n_pre = (Zlength (text)))) (PreH10 : (k_pre = cursor)) (PreH11 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH12 : (1 < p)) (PreH13 : (p <= n_pre)) (PreH14 : (0 <= t)) (PreH15 : (t < (3 * n_pre ))) (PreH16 : (0 <= (t + 1 ))) (PreH17 : ((t + 1 ) < (3 * n_pre ))) (PreH18 : ((t + (2 * (p - 1 ) ) ) < (3 * n_pre ))) (PreH19 : (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH20 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH21 : (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows_2 )) (PreH22 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH23 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (0 <= (p - 1 )) ” 
  &&  “ ((p - 1 ) <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p - 1 ) > 0) -> (((t + 1 ) + ((2 * (p - 1 ) ) - 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 )))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge LeftAction (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= n_pre)) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 100)) (PreH9 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH10 : (n_pre = (Zlength (text)))) (PreH11 : (k_pre = cursor)) (PreH12 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH13 : (1 < p)) (PreH14 : (p <= n_pre)) (PreH15 : (0 <= t)) (PreH16 : (t < (3 * n_pre ))) (PreH17 : (0 <= (t + 1 ))) (PreH18 : ((t + 1 ) < (3 * n_pre ))) (PreH19 : ((t + (2 * (p - 1 ) ) ) < (3 * n_pre ))) (PreH20 : (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH21 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH22 : (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows_2 )) (PreH23 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH24 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (0 <= (p - 1 )) ” 
  &&  “ ((p - 1 ) <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p - 1 ) > 0) -> (((t + 1 ) + ((2 * (p - 1 ) ) - 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 )))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
).

Definition solver_entail_wit_14_2 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (0 <= (p - 1 )) ” 
  &&  “ ((p - 1 ) <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p - 1 ) > 0) -> (((t + 1 ) + ((2 * (p - 1 ) ) - 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 )))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows_2: (@list (@list Z))) (p: Z) (t: Z) (after: (@list Z))  __default__List_Z (PreH1 : (p <= 1)) (PreH2 : ((Zlength (after)) = 8)) (PreH3 : (ActionSlotBridge (PrintAction ((Znth (p - 1 ) text 0))) (Znth t rows_2 __default__List_Z) after )) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= 8)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100)) (PreH10 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((((((65 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 90)) \/ ((48 <= (Znth j_2 text 0)) /\ ((Znth j_2 text 0) <= 57))) \/ ((Znth j_2 text 0) = 46)) \/ ((Znth j_2 text 0) = 33)) \/ ((Znth j_2 text 0) = 44)) \/ ((Znth j_2 text 0) = 63)))) (PreH11 : (n_pre = (Zlength (text)))) (PreH12 : (k_pre = cursor)) (PreH13 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH14 : (1 <= p)) (PreH15 : (p <= n_pre)) (PreH16 : (0 <= t)) (PreH17 : (t < (3 * n_pre ))) (PreH18 : (0 <= (t + 1 ))) (PreH19 : ((t + 1 ) < (3 * n_pre ))) (PreH20 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH21 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH22 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH23 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH24 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows_2 )) (PreH25 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < (3 * n_pre ))) -> ((Zlength ((Znth i_2 rows_2 __default__List_Z))) = 8))) (PreH26 : ((Zlength ((Znth t rows_2 __default__List_Z))) = 8)) ,
  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 after )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows_2 )
|--
  EX (rows: (@list (@list Z))) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (0 <= (p - 1 )) ” 
  &&  “ ((p - 1 ) <= n_pre) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((p - 1 ) > 0) -> (((t + 1 ) + ((2 * (p - 1 ) ) - 1 ) ) < (3 * n_pre ))) ” 
  &&  “ ((t + 1 ) = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 )))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) ((p - 1 ))))) (t + 1 ) out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ”
  &&  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
).

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p > n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= (n_pre + 1 ))) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p <= n_pre) -> ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH18 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
|--
  EX (out_after: (@list (@list Z)))  (out_spec: (@list (Z * Z))) ,
  “ (Spec cursor text out_spec ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) out_spec t out_before out_after ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_after )
) \/
(
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p > n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= (n_pre + 1 ))) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p <= n_pre) -> ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH18 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) ,
  TT && emp 
|--
  EX (out_spec: (@list (Z * Z))) ,
  “ (Spec cursor text out_spec ) ” 
  &&  “ (SolverOutputBridge (3 * (Zlength (text)) ) out_spec (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))) out_before rows ) ”
  &&  emp
).

Definition solver_return_wit_2 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p < 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (0 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p > 0) -> ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH18 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 rows )
|--
  EX (out_after: (@list (@list Z)))  (out_spec: (@list (Z * Z))) ,
  “ (Spec cursor text out_spec ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) out_spec t out_before out_after ) ”
  &&  (CharArray.full s_pre n_pre text )
  **  (CharArray2.full out_pre (3 * n_pre ) 8 out_after )
) \/
(
forall (k_pre: Z) (n_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (t: Z) (p: Z)  __default__List_Z (PreH1 : (p < 1)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (0 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : ((p > 0) -> ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )))) (PreH15 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH16 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH17 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH18 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) ,
  TT && emp 
|--
  EX (out_spec: (@list (Z * Z))) ,
  “ (Spec cursor text out_spec ) ” 
  &&  “ (SolverOutputBridge (3 * (Zlength (text)) ) out_spec (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))) out_before rows ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1_pure := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH10 : (1 < p)) (PreH11 : (p <= k_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH18 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH10 : (1 < p)) (PreH11 : (p <= k_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((LeftWalkPlan (k_pre) (p)))))) (PreH18 : (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (1 < p) ” 
  &&  “ (p <= k_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + (p - 1 ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((LeftWalkPlan (k_pre) (p))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (LeftWalkPlan (k_pre) (p)) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= 8) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (((s_pre + ((p - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (p - 1 ) text 0))
  **  (CharArray.missing_i s_pre (p - 1 ) 0 n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
.

Definition solver_partial_solve_wit_3_pure := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH17 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH18 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH19 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH20 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH21 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH22 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH17 : ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre ))) (PreH18 : (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))))))) (PreH19 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH20 : (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows )) (PreH21 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH22 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p < n_pre) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * (n_pre - p ) ) + 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4_pure := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p < n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH17 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH18 : (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
.

Definition solver_partial_solve_wit_4_aux := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) <= (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p < n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH17 : (Spec k_pre text (LeftFirstPlan (k_pre) (text)) )) (PreH18 : (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) <= (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((t + (2 * (n_pre - p ) ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z))))))))) ” 
  &&  “ (Spec k_pre text (LeftFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((app ((LeftWalkPlan (k_pre) (1))) ((ForwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5_pure := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH10 : (k_pre <= p)) (PreH11 : (p < n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH18 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
.

Definition solver_partial_solve_wit_5_aux := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH10 : (k_pre <= p)) (PreH11 : (p < n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((RightWalkPlan (k_pre) (p)))))) (PreH18 : (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (k_pre <= p) ” 
  &&  “ (p < n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ (((t + (n_pre - p ) ) + ((2 * n_pre ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((RightWalkPlan (k_pre) (p))))) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (RightWalkPlan (k_pre) (p)) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Definition solver_partial_solve_wit_6 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (1 <= p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH16 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH17 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH18 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH19 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH20 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH21 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ (0 <= 8) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (((s_pre + ((p - 1 ) * sizeof(CHAR)))) # Char  |-> (Znth (p - 1 ) text 0))
  **  (CharArray.missing_i s_pre (p - 1 ) 0 n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
.

Definition solver_partial_solve_wit_7_pure := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH17 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH18 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH19 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH20 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH21 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH22 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
.

Definition solver_partial_solve_wit_7_aux := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (0 <= 8)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH7 : (n_pre = (Zlength (text)))) (PreH8 : (k_pre = cursor)) (PreH9 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH10 : (1 <= p)) (PreH11 : (p <= n_pre)) (PreH12 : (0 <= t)) (PreH13 : (t < (3 * n_pre ))) (PreH14 : (0 <= (t + 1 ))) (PreH15 : ((t + 1 ) < (3 * n_pre ))) (PreH16 : ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre ))))) (PreH17 : ((t + ((2 * p ) - 1 ) ) < (3 * n_pre ))) (PreH18 : (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))))))) (PreH19 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH20 : (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows )) (PreH21 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH22 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((p > 1) -> ((0 <= (t + 2 )) /\ ((t + 2 ) < (3 * n_pre )))) ” 
  &&  “ ((t + ((2 * p ) - 1 ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p)))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
.

Definition solver_partial_solve_wit_7 := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux.

Definition solver_partial_solve_wit_8_pure := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (1 < p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((t + (2 * (p - 1 ) ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH17 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH18 : (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
.

Definition solver_partial_solve_wit_8_aux := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (s_pre: Z) (out_before: (@list (@list Z))) (text: (@list Z)) (cursor: Z) (rows: (@list (@list Z))) (p: Z) (t: Z)  __default__List_Z (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63)))) (PreH6 : (n_pre = (Zlength (text)))) (PreH7 : (k_pre = cursor)) (PreH8 : ((k_pre - 1 ) > (n_pre - k_pre ))) (PreH9 : (1 < p)) (PreH10 : (p <= n_pre)) (PreH11 : (0 <= t)) (PreH12 : (t < (3 * n_pre ))) (PreH13 : (0 <= (t + 1 ))) (PreH14 : ((t + 1 ) < (3 * n_pre ))) (PreH15 : ((t + (2 * (p - 1 ) ) ) < (3 * n_pre ))) (PreH16 : (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))))))) (PreH17 : (Spec k_pre text (RightFirstPlan (k_pre) (text)) )) (PreH18 : (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows )) (PreH19 : forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8))) (PreH20 : ((Zlength ((Znth t rows __default__List_Z))) = 8)) ,
  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
  **  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
|--
  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((((((65 <= (Znth j text 0)) /\ ((Znth j text 0) <= 90)) \/ ((48 <= (Znth j text 0)) /\ ((Znth j text 0) <= 57))) \/ ((Znth j text 0) = 46)) \/ ((Znth j text 0) = 33)) \/ ((Znth j text 0) = 44)) \/ ((Znth j text 0) = 63))) ” 
  &&  “ (n_pre = (Zlength (text))) ” 
  &&  “ (k_pre = cursor) ” 
  &&  “ ((k_pre - 1 ) > (n_pre - k_pre )) ” 
  &&  “ (1 < p) ” 
  &&  “ (p <= n_pre) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < (3 * n_pre )) ” 
  &&  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) < (3 * n_pre )) ” 
  &&  “ ((t + (2 * (p - 1 ) ) ) < (3 * n_pre )) ” 
  &&  “ (t = (Zlength ((app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z))))))))) ” 
  &&  “ (Spec k_pre text (RightFirstPlan (k_pre) (text)) ) ” 
  &&  “ (SolverOutputBridge (3 * n_pre ) (app ((app ((RightWalkPlan (k_pre) (n_pre))) ((BackwardSweepPlan (text) (p))))) ((cons ((PrintAction ((Znth (p - 1 ) text 0)))) ((@nil (Z * Z)))))) t out_before rows ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (3 * n_pre ))) -> ((Zlength ((Znth i rows __default__List_Z))) = 8)) ” 
  &&  “ ((Zlength ((Znth t rows __default__List_Z))) = 8) ”
  &&  (CharArray.full ((out_pre + (t * (sizeof(CHAR) * 8))) + (0 * sizeof(CHAR))) 8 (Znth t rows __default__List_Z) )
  **  (CharArray.full s_pre n_pre text )
  **  (CharArray2.missing_i out_pre t 0 (3 * n_pre ) 8 rows )
.

Definition solver_partial_solve_wit_8 := solver_partial_solve_wit_8_pure -> solver_partial_solve_wit_8_aux.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_write_left_safety_wit_1 : write_left_safety_wit_1.
Axiom proof_of_write_left_safety_wit_2 : write_left_safety_wit_2.
Axiom proof_of_write_left_safety_wit_3 : write_left_safety_wit_3.
Axiom proof_of_write_left_safety_wit_4 : write_left_safety_wit_4.
Axiom proof_of_write_left_safety_wit_5 : write_left_safety_wit_5.
Axiom proof_of_write_left_safety_wit_6 : write_left_safety_wit_6.
Axiom proof_of_write_left_safety_wit_7 : write_left_safety_wit_7.
Axiom proof_of_write_left_safety_wit_8 : write_left_safety_wit_8.
Axiom proof_of_write_left_safety_wit_9 : write_left_safety_wit_9.
Axiom proof_of_write_left_safety_wit_10 : write_left_safety_wit_10.
Axiom proof_of_write_left_return_wit_1 : write_left_return_wit_1.
Axiom proof_of_write_left_partial_solve_wit_1 : write_left_partial_solve_wit_1.
Axiom proof_of_write_left_partial_solve_wit_2 : write_left_partial_solve_wit_2.
Axiom proof_of_write_left_partial_solve_wit_3 : write_left_partial_solve_wit_3.
Axiom proof_of_write_left_partial_solve_wit_4 : write_left_partial_solve_wit_4.
Axiom proof_of_write_left_partial_solve_wit_5 : write_left_partial_solve_wit_5.
Axiom proof_of_write_right_safety_wit_1 : write_right_safety_wit_1.
Axiom proof_of_write_right_safety_wit_2 : write_right_safety_wit_2.
Axiom proof_of_write_right_safety_wit_3 : write_right_safety_wit_3.
Axiom proof_of_write_right_safety_wit_4 : write_right_safety_wit_4.
Axiom proof_of_write_right_safety_wit_5 : write_right_safety_wit_5.
Axiom proof_of_write_right_safety_wit_6 : write_right_safety_wit_6.
Axiom proof_of_write_right_safety_wit_7 : write_right_safety_wit_7.
Axiom proof_of_write_right_safety_wit_8 : write_right_safety_wit_8.
Axiom proof_of_write_right_safety_wit_9 : write_right_safety_wit_9.
Axiom proof_of_write_right_safety_wit_10 : write_right_safety_wit_10.
Axiom proof_of_write_right_safety_wit_11 : write_right_safety_wit_11.
Axiom proof_of_write_right_safety_wit_12 : write_right_safety_wit_12.
Axiom proof_of_write_right_return_wit_1 : write_right_return_wit_1.
Axiom proof_of_write_right_partial_solve_wit_1 : write_right_partial_solve_wit_1.
Axiom proof_of_write_right_partial_solve_wit_2 : write_right_partial_solve_wit_2.
Axiom proof_of_write_right_partial_solve_wit_3 : write_right_partial_solve_wit_3.
Axiom proof_of_write_right_partial_solve_wit_4 : write_right_partial_solve_wit_4.
Axiom proof_of_write_right_partial_solve_wit_5 : write_right_partial_solve_wit_5.
Axiom proof_of_write_right_partial_solve_wit_6 : write_right_partial_solve_wit_6.
Axiom proof_of_write_print_safety_wit_1 : write_print_safety_wit_1.
Axiom proof_of_write_print_safety_wit_2 : write_print_safety_wit_2.
Axiom proof_of_write_print_safety_wit_3 : write_print_safety_wit_3.
Axiom proof_of_write_print_safety_wit_4 : write_print_safety_wit_4.
Axiom proof_of_write_print_safety_wit_5 : write_print_safety_wit_5.
Axiom proof_of_write_print_safety_wit_6 : write_print_safety_wit_6.
Axiom proof_of_write_print_safety_wit_7 : write_print_safety_wit_7.
Axiom proof_of_write_print_safety_wit_8 : write_print_safety_wit_8.
Axiom proof_of_write_print_safety_wit_9 : write_print_safety_wit_9.
Axiom proof_of_write_print_safety_wit_10 : write_print_safety_wit_10.
Axiom proof_of_write_print_safety_wit_11 : write_print_safety_wit_11.
Axiom proof_of_write_print_safety_wit_12 : write_print_safety_wit_12.
Axiom proof_of_write_print_safety_wit_13 : write_print_safety_wit_13.
Axiom proof_of_write_print_safety_wit_14 : write_print_safety_wit_14.
Axiom proof_of_write_print_safety_wit_15 : write_print_safety_wit_15.
Axiom proof_of_write_print_return_wit_1 : write_print_return_wit_1.
Axiom proof_of_write_print_partial_solve_wit_1 : write_print_partial_solve_wit_1.
Axiom proof_of_write_print_partial_solve_wit_2 : write_print_partial_solve_wit_2.
Axiom proof_of_write_print_partial_solve_wit_3 : write_print_partial_solve_wit_3.
Axiom proof_of_write_print_partial_solve_wit_4 : write_print_partial_solve_wit_4.
Axiom proof_of_write_print_partial_solve_wit_5 : write_print_partial_solve_wit_5.
Axiom proof_of_write_print_partial_solve_wit_6 : write_print_partial_solve_wit_6.
Axiom proof_of_write_print_partial_solve_wit_7 : write_print_partial_solve_wit_7.
Axiom proof_of_write_print_partial_solve_wit_8 : write_print_partial_solve_wit_8.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8_pure : solver_partial_solve_wit_8_pure.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.

End VC_Correct.
