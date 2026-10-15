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
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_proof.

(*----- Function beats -----*)

Definition beats_safety_wit_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (PreH1 : (0 <= ia_pre)) (PreH2 : (ia_pre < 3)) (PreH3 : (0 <= ib_pre)) (PreH4 : (ib_pre < 3)) (PreH5 : (ia_pre <> ib_pre)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "ac" ) )) # Char  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition beats_safety_wit_2 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (0 <= ia_pre)) (PreH2 : (ia_pre < 3)) (PreH3 : (0 <= ib_pre)) (PreH4 : (ib_pre < 3)) (PreH5 : (ia_pre <> ib_pre)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "bc" ) )) # Char  |->_)
  **  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) )
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition beats_safety_wit_3 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (0 <= ia_pre)) (PreH2 : (ia_pre < 3)) (PreH3 : (0 <= ib_pre)) (PreH4 : (ib_pre < 3)) (PreH5 : (ia_pre <> ib_pre)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (114 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 114) ”
.

Definition beats_safety_wit_4 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH2 : (0 <= ia_pre)) (PreH3 : (ia_pre < 3)) (PreH4 : (0 <= ib_pre)) (PreH5 : (ib_pre < 3)) (PreH6 : (ia_pre <> ib_pre)) (PreH7 : ((Zlength (players)) = 3)) (PreH8 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH9 : ((Zlength (game_mem)) = 3)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (115 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 115) ”
.

Definition beats_safety_wit_5 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH3 : (0 <= ia_pre)) (PreH4 : (ia_pre < 3)) (PreH5 : (0 <= ib_pre)) (PreH6 : (ib_pre < 3)) (PreH7 : (ia_pre <> ib_pre)) (PreH8 : ((Zlength (players)) = 3)) (PreH9 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH10 : ((Zlength (game_mem)) = 3)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (115 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 115) ”
.

Definition beats_safety_wit_6 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH2 : (0 <= ia_pre)) (PreH3 : (ia_pre < 3)) (PreH4 : (0 <= ib_pre)) (PreH5 : (ib_pre < 3)) (PreH6 : (ia_pre <> ib_pre)) (PreH7 : ((Zlength (players)) = 3)) (PreH8 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH9 : ((Zlength (game_mem)) = 3)) (PreH10 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (115 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 115) ”
.

Definition beats_safety_wit_7 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH2 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ False ”
.

Definition beats_safety_wit_8 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH3 : (0 <= ia_pre)) (PreH4 : (ia_pre < 3)) (PreH5 : (0 <= ib_pre)) (PreH6 : (ib_pre < 3)) (PreH7 : (ia_pre <> ib_pre)) (PreH8 : ((Zlength (players)) = 3)) (PreH9 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH10 : ((Zlength (game_mem)) = 3)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (112 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 112) ”
.

Definition beats_safety_wit_9 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH3 : (0 <= ia_pre)) (PreH4 : (ia_pre < 3)) (PreH5 : (0 <= ib_pre)) (PreH6 : (ib_pre < 3)) (PreH7 : (ia_pre <> ib_pre)) (PreH8 : ((Zlength (players)) = 3)) (PreH9 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH10 : ((Zlength (game_mem)) = 3)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (112 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 112) ”
.

Definition beats_safety_wit_10 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH2 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (112 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 112) ”
.

Definition beats_safety_wit_11 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (112 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 112) ”
.

Definition beats_safety_wit_12 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ False ”
.

Definition beats_safety_wit_13 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH2 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ False ”
.

Definition beats_safety_wit_14 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
  **  ((( &( "bc" ) )) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (114 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 114) ”
.

Definition beats_return_wit_1 := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ” 
  &&  “ ((1 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
).

Definition beats_return_wit_1_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ”
.

Definition beats_return_wit_1_split_goal_spatial := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition beats_return_wit_2 := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 115)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH3 : (0 <= ia_pre)) (PreH4 : (ia_pre < 3)) (PreH5 : (0 <= ib_pre)) (PreH6 : (ib_pre < 3)) (PreH7 : (ia_pre <> ib_pre)) (PreH8 : ((Zlength (players)) = 3)) (PreH9 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH10 : ((Zlength (game_mem)) = 3)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ” 
  &&  “ ((1 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 115)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH3 : (0 <= ia_pre)) (PreH4 : (ia_pre < 3)) (PreH5 : (0 <= ib_pre)) (PreH6 : (ib_pre < 3)) (PreH7 : (ia_pre <> ib_pre)) (PreH8 : ((Zlength (players)) = 3)) (PreH9 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH10 : ((Zlength (game_mem)) = 3)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
).

Definition beats_return_wit_2_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 115)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH3 : (0 <= ia_pre)) (PreH4 : (ia_pre < 3)) (PreH5 : (0 <= ib_pre)) (PreH6 : (ib_pre < 3)) (PreH7 : (ia_pre <> ib_pre)) (PreH8 : ((Zlength (players)) = 3)) (PreH9 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH10 : ((Zlength (game_mem)) = 3)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ”
.

Definition beats_return_wit_2_split_goal_spatial := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 115)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH3 : (0 <= ia_pre)) (PreH4 : (ia_pre < 3)) (PreH5 : (0 <= ib_pre)) (PreH6 : (ib_pre < 3)) (PreH7 : (ia_pre <> ib_pre)) (PreH8 : ((Zlength (players)) = 3)) (PreH9 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH10 : ((Zlength (game_mem)) = 3)) (PreH11 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition beats_return_wit_3 := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ” 
  &&  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
).

Definition beats_return_wit_3_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
.

Definition beats_return_wit_3_split_goal_spatial := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition beats_return_wit_4 := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ” 
  &&  “ ((1 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
).

Definition beats_return_wit_4_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((1 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ”
.

Definition beats_return_wit_4_split_goal_spatial := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) = 114)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition beats_return_wit_5 := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ” 
  &&  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
).

Definition beats_return_wit_5_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
.

Definition beats_return_wit_5_split_goal_spatial := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH4 : (0 <= ia_pre)) (PreH5 : (ia_pre < 3)) (PreH6 : (0 <= ib_pre)) (PreH7 : (ib_pre < 3)) (PreH8 : (ia_pre <> ib_pre)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition beats_return_wit_6 := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ” 
  &&  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
).

Definition beats_return_wit_6_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
.

Definition beats_return_wit_6_split_goal_spatial := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 115)) (PreH3 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition beats_return_wit_7 := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 <> 0) -> (Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) )) ” 
  &&  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
).

Definition beats_return_wit_7_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  “ ((0 = 0) -> ~((Beats (Znth (ia_pre) (players) ((@nil Z))) (Znth (ib_pre) (players) ((@nil Z))) ))) ”
.

Definition beats_return_wit_7_split_goal_spatial := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 112)) (PreH2 : ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)) <> 112)) (PreH3 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) = 115)) (PreH4 : ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)) <> 114)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ib_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0))))) ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)))) ((Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)))) )
|--
  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition beats_partial_solve_wit_1_pure := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (0 <= ia_pre)) (PreH2 : (ia_pre < 3)) (PreH3 : (0 <= ib_pre)) (PreH4 : (ib_pre < 3)) (PreH5 : (ia_pre <> ib_pre)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "ac" ) )) # Char  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (Array2.mixed_def (Znth ia_pre game_mem __default__List__App_option_Z) 0 ) ”
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (ib_pre <= INT_MAX)) (PreH2 : (ia_pre <= INT_MAX)) (PreH3 : (ib_pre >= INT_MIN)) (PreH4 : (ia_pre >= INT_MIN)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "ac" ) )) # Char  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (Array2.mixed_def (Znth ia_pre game_mem __default__List__App_option_Z) 0 ) ”
).

Definition beats_partial_solve_wit_1_pure_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (ib_pre <= INT_MAX)) (PreH2 : (ia_pre <= INT_MAX)) (PreH3 : (ib_pre >= INT_MIN)) (PreH4 : (ia_pre >= INT_MIN)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "ac" ) )) # Char  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (Array2.mixed_def (Znth ia_pre game_mem __default__List__App_option_Z) 0 ) ”
.

Definition beats_partial_solve_wit_1_aux := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (0 <= ia_pre)) (PreH2 : (ia_pre < 3)) (PreH3 : (0 <= ib_pre)) (PreH4 : (ib_pre < 3)) (PreH5 : (ia_pre <> ib_pre)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (Array2.mixed_def (Znth ia_pre game_mem __default__List__App_option_Z) 0 ) ” 
  &&  “ (0 <= ia_pre) ” 
  &&  “ (ia_pre < 3) ” 
  &&  “ (0 <= ib_pre) ” 
  &&  “ (ib_pre < 3) ” 
  &&  “ (ia_pre <> ib_pre) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
  &&  ((((g_pre + (ia_pre * (sizeof(CHAR) * 16))) + (0 * sizeof(CHAR)))) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  (CharArray.mixed_missing_i (g_pre + (ia_pre * (sizeof(CHAR) * 16))) 0 0 16 (Znth ia_pre game_mem __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i g_pre ia_pre 0 3 16 game_mem )
.

Definition beats_partial_solve_wit_1 := beats_partial_solve_wit_1_pure -> beats_partial_solve_wit_1_aux.

Definition beats_partial_solve_wit_2_pure := 
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (0 <= ia_pre)) (PreH2 : (ia_pre < 3)) (PreH3 : (0 <= ib_pre)) (PreH4 : (ib_pre < 3)) (PreH5 : (ia_pre <> ib_pre)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "bc" ) )) # Char  |->_)
  **  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) )
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (Array2.mixed_def (Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z) 0 ) ”
) \/
(
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (ib_pre <= INT_MAX)) (PreH2 : (ia_pre <= INT_MAX)) (PreH3 : (ib_pre >= INT_MIN)) (PreH4 : (ia_pre >= INT_MIN)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "bc" ) )) # Char  |->_)
  **  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) )
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (Array2.mixed_def (Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z) 0 ) ”
).

Definition beats_partial_solve_wit_2_pure_split_goal_1 := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (ib_pre <= INT_MAX)) (PreH2 : (ia_pre <= INT_MAX)) (PreH3 : (ib_pre >= INT_MIN)) (PreH4 : (ia_pre >= INT_MIN)) (PreH5 : (0 <= ia_pre)) (PreH6 : (ia_pre < 3)) (PreH7 : (0 <= ib_pre)) (PreH8 : (ib_pre < 3)) (PreH9 : (ia_pre <> ib_pre)) (PreH10 : ((Zlength (players)) = 3)) (PreH11 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH12 : ((Zlength (game_mem)) = 3)) (PreH13 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "bc" ) )) # Char  |->_)
  **  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) )
  **  ((( &( "ac" ) )) # Char  |-> (Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0)))
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "ia" ) )) # Int  |-> ia_pre)
  **  ((( &( "ib" ) )) # Int  |-> ib_pre)
|--
  “ (Array2.mixed_def (Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z) 0 ) ”
.

Definition beats_partial_solve_wit_2_aux := 
forall (ib_pre: Z) (ia_pre: Z) (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z)))  __default__List__App_option_Z (PreH1 : (0 <= ia_pre)) (PreH2 : (ia_pre < 3)) (PreH3 : (0 <= ib_pre)) (PreH4 : (ib_pre < 3)) (PreH5 : (ia_pre <> ib_pre)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) )
|--
  “ (Array2.mixed_def (Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z) 0 ) ” 
  &&  “ (0 <= ia_pre) ” 
  &&  “ (ia_pre < 3) ” 
  &&  “ (0 <= ib_pre) ” 
  &&  “ (ib_pre < 3) ” 
  &&  “ (ia_pre <> ib_pre) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
  &&  ((((g_pre + (ib_pre * (sizeof(CHAR) * 16))) + (0 * sizeof(CHAR)))) # Char  |-> (Array2.mixed_val ((Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z)) (0)))
  **  (CharArray.mixed_missing_i (g_pre + (ib_pre * (sizeof(CHAR) * 16))) 0 0 16 (Znth ib_pre (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) __default__List__App_option_Z) )
  **  (CharArray2.mixed_missing_i g_pre ib_pre 0 3 16 (Array2.replace_mixed_row (ia_pre) ((replace_Znth (0) ((Some ((Array2.mixed_val ((Znth ia_pre game_mem __default__List__App_option_Z)) (0))))) ((Znth ia_pre game_mem __default__List__App_option_Z)))) (game_mem)) )
.

Definition beats_partial_solve_wit_2 := beats_partial_solve_wit_2_pure -> beats_partial_solve_wit_2_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (PreH1 : ((Zlength (players)) = 3)) (PreH2 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH3 : ((Zlength (game_mem)) = 3)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> (((((Zlength ((Znth (i) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (i) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (j: Z) , (((0 <= j) /\ (j < (Zlength ((Znth (i) (players) ((@nil Z))))))) -> ((Znth (j) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (i) (players) ((@nil Z)))))) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 3)) (PreH3 : ((Zlength (players)) = 3)) (PreH4 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH5 : ((Zlength (game_mem)) = 3)) (PreH6 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_3 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (((i + 1 ) <> (INT_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition solver_safety_wit_4 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_7 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (((i + 2 ) <> (INT_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition solver_safety_wit_8 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition solver_safety_wit_9 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_10 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_11 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH10 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH11 : (i < 3)) (PreH12 : (0 <= i)) (PreH13 : (i <= 3)) (PreH14 : ((Zlength (players)) = 3)) (PreH15 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH16 : ((Zlength (game_mem)) = 3)) (PreH17 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH6 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH11 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH12 : (i < 3)) (PreH13 : (0 <= i)) (PreH14 : (i <= 3)) (PreH15 : ((Zlength (players)) = 3)) (PreH16 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH17 : ((Zlength (game_mem)) = 3)) (PreH18 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (70 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 70) ”
.

Definition solver_safety_wit_13 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH6 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH11 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH12 : (i < 3)) (PreH13 : (0 <= i)) (PreH14 : (i <= 3)) (PreH15 : ((Zlength (players)) = 3)) (PreH16 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH17 : ((Zlength (game_mem)) = 3)) (PreH18 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i = 1)) (PreH2 : (i <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH12 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH13 : (i < 3)) (PreH14 : (0 <= i)) (PreH15 : (i <= 3)) (PreH16 : ((Zlength (players)) = 3)) (PreH17 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH18 : ((Zlength (game_mem)) = 3)) (PreH19 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (77 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 77) ”
.

Definition solver_safety_wit_15 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i <> 1)) (PreH2 : (i <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH12 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH13 : (i < 3)) (PreH14 : (0 <= i)) (PreH15 : (i <= 3)) (PreH16 : ((Zlength (players)) = 3)) (PreH17 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH18 : ((Zlength (game_mem)) = 3)) (PreH19 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (83 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 83) ”
.

Definition solver_safety_wit_16 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition solver_safety_wit_17 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_18 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH10 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH11 : (i < 3)) (PreH12 : (0 <= i)) (PreH13 : (i <= 3)) (PreH14 : ((Zlength (players)) = 3)) (PreH15 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH16 : ((Zlength (game_mem)) = 3)) (PreH17 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (PreH1 : ((Zlength (players)) = 3)) (PreH2 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH3 : ((Zlength (game_mem)) = 3)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> (((((Zlength ((Znth (i) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (i) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (j: Z) , (((0 <= j) /\ (j < (Zlength ((Znth (i) (players) ((@nil Z))))))) -> ((Znth (j) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (i) (players) ((@nil Z)))))) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (PreH1 : ((Zlength (players)) = 3)) (PreH2 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH3 : ((Zlength (game_mem)) = 3)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> (((((Zlength ((Znth (i) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (i) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (j: Z) , (((0 <= j) /\ (j < (Zlength ((Znth (i) (players) ((@nil Z))))))) -> ((Znth (j) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (i) (players) ((@nil Z)))))) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (PreH1 : ((Zlength (players)) = 3)) (PreH2 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH3 : ((Zlength (game_mem)) = 3)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> (((((Zlength ((Znth (i) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (i) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (j: Z) , (((0 <= j) /\ (j < (Zlength ((Znth (i) (players) ((@nil Z))))))) -> ((Znth (j) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (j) ((Znth (i) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (i) (players) ((@nil Z)))))) ((Znth (i) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))
.

Definition solver_entail_wit_2_1 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition solver_entail_wit_2_2 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH10 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH11 : (i < 3)) (PreH12 : (0 <= i)) (PreH13 : (i <= 3)) (PreH14 : ((Zlength (players)) = 3)) (PreH15 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH16 : ((Zlength (game_mem)) = 3)) (PreH17 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition solver_return_wit_1 := 
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (63 = (Znth 0 result 0)) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  TT && emp 
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (63 = (Znth 0 result 0)) ”
  &&  emp
).

Definition solver_return_wit_2 := 
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH6 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH11 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH12 : (i < 3)) (PreH13 : (0 <= i)) (PreH14 : (i <= 3)) (PreH15 : ((Zlength (players)) = 3)) (PreH16 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH17 : ((Zlength (game_mem)) = 3)) (PreH18 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (70 = (Znth 0 result 0)) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH6 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH7 : (retval <> 0)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH11 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH12 : (i < 3)) (PreH13 : (0 <= i)) (PreH14 : (i <= 3)) (PreH15 : ((Zlength (players)) = 3)) (PreH16 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH17 : ((Zlength (game_mem)) = 3)) (PreH18 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  TT && emp 
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (70 = (Znth 0 result 0)) ”
  &&  emp
).

Definition solver_return_wit_3 := 
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i = 1)) (PreH2 : (i <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH12 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH13 : (i < 3)) (PreH14 : (0 <= i)) (PreH15 : (i <= 3)) (PreH16 : ((Zlength (players)) = 3)) (PreH17 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH18 : ((Zlength (game_mem)) = 3)) (PreH19 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (77 = (Znth 0 result 0)) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i = 1)) (PreH2 : (i <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH12 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH13 : (i < 3)) (PreH14 : (0 <= i)) (PreH15 : (i <= 3)) (PreH16 : ((Zlength (players)) = 3)) (PreH17 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH18 : ((Zlength (game_mem)) = 3)) (PreH19 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  TT && emp 
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (77 = (Znth 0 result 0)) ”
  &&  emp
).

Definition solver_return_wit_4 := 
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i <> 1)) (PreH2 : (i <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH12 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH13 : (i < 3)) (PreH14 : (0 <= i)) (PreH15 : (i <= 3)) (PreH16 : ((Zlength (players)) = 3)) (PreH17 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH18 : ((Zlength (game_mem)) = 3)) (PreH19 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (83 = (Znth 0 result 0)) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
) \/
(
forall (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (i <> 1)) (PreH2 : (i <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : ((retval_2 <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval_2 = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (retval <> 0)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH12 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH13 : (i < 3)) (PreH14 : (0 <= i)) (PreH15 : (i <= 3)) (PreH16 : ((Zlength (players)) = 3)) (PreH17 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH18 : ((Zlength (game_mem)) = 3)) (PreH19 : forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((Zlength ((Znth (row) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH20 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  TT && emp 
|--
  EX (result: (@list Z)) ,
  “ (Spec (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) result ) ” 
  &&  “ (83 = (Znth 0 result 0)) ”
  &&  emp
).

Definition solver_partial_solve_wit_1_pure := 
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (i <> ((i + 1 ) % ( 3 ) )) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) < 3) ” 
  &&  “ (0 <= ((i + 1 ) % ( 3 ) )) ”
) \/
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (i < 3)) (PreH4 : (0 <= i)) (PreH5 : (i <= 3)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= ((i + 1 ) % ( 3 ) )) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) < 3) ” 
  &&  “ (i <> ((i + 1 ) % ( 3 ) )) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (i < 3)) (PreH4 : (0 <= i)) (PreH5 : (i <= 3)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= ((i + 1 ) % ( 3 ) )) ”
.

Definition solver_partial_solve_wit_1_pure_split_goal_2 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (i < 3)) (PreH4 : (0 <= i)) (PreH5 : (i <= 3)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (((i + 1 ) % ( 3 ) ) < 3) ”
.

Definition solver_partial_solve_wit_1_pure_split_goal_3 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (i < 3)) (PreH4 : (0 <= i)) (PreH5 : (i <= 3)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (i <> ((i + 1 ) % ( 3 ) )) ”
.

Definition solver_partial_solve_wit_1_pure_split_goal_4 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (i < 3)) (PreH4 : (0 <= i)) (PreH5 : (i <= 3)) (PreH6 : ((Zlength (players)) = 3)) (PreH7 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH8 : ((Zlength (game_mem)) = 3)) (PreH9 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= i)) (PreH3 : (i <= 3)) (PreH4 : ((Zlength (players)) = 3)) (PreH5 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH6 : ((Zlength (game_mem)) = 3)) (PreH7 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (i <> ((i + 1 ) % ( 3 ) )) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) < 3) ” 
  &&  “ (0 <= ((i + 1 ) % ( 3 ) )) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (i <> ((i + 2 ) % ( 3 ) )) ” 
  &&  “ (((i + 2 ) % ( 3 ) ) < 3) ” 
  &&  “ (0 <= ((i + 2 ) % ( 3 ) )) ”
) \/
(
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (i < 3)) (PreH9 : (0 <= i)) (PreH10 : (i <= 3)) (PreH11 : ((Zlength (players)) = 3)) (PreH12 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH13 : ((Zlength (game_mem)) = 3)) (PreH14 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= ((i + 2 ) % ( 3 ) )) ” 
  &&  “ (((i + 2 ) % ( 3 ) ) < 3) ” 
  &&  “ (i <> ((i + 2 ) % ( 3 ) )) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (i < 3)) (PreH9 : (0 <= i)) (PreH10 : (i <= 3)) (PreH11 : ((Zlength (players)) = 3)) (PreH12 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH13 : ((Zlength (game_mem)) = 3)) (PreH14 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= ((i + 2 ) % ( 3 ) )) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_2 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (i < 3)) (PreH9 : (0 <= i)) (PreH10 : (i <= 3)) (PreH11 : ((Zlength (players)) = 3)) (PreH12 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH13 : ((Zlength (game_mem)) = 3)) (PreH14 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (((i + 2 ) % ( 3 ) ) < 3) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_3 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (i < 3)) (PreH9 : (0 <= i)) (PreH10 : (i <= 3)) (PreH11 : ((Zlength (players)) = 3)) (PreH12 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH13 : ((Zlength (game_mem)) = 3)) (PreH14 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (i <> ((i + 2 ) % ( 3 ) )) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_4 := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (i >= INT_MIN)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH7 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH8 : (i < 3)) (PreH9 : (0 <= i)) (PreH10 : (i <= 3)) (PreH11 : ((Zlength (players)) = 3)) (PreH12 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH13 : ((Zlength (game_mem)) = 3)) (PreH14 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
  **  ((( &( "g" ) )) # Ptr  |-> g_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (g_pre: Z) (game_mem: (@list (@list (@option Z)))) (players: (@list (@list Z))) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) (PreH5 : ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )))) (PreH6 : (i < 3)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (players)) = 3)) (PreH10 : (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) )) (PreH11 : ((Zlength (game_mem)) = 3)) (PreH12 : forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0)))))) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) ))))) ,
  (CharArray2.mixed_full g_pre 3 16 game_mem )
|--
  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row: Z) , (((0 <= row) /\ (row < 3)) -> (((((0 < (Zlength ((Znth (row) (players) ((@nil Z)))))) /\ ((Zlength ((Znth (row) (players) ((@nil Z))))) < 16)) /\ ((Zlength ((Znth (row) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col: Z) , (((0 <= col) /\ (col < (Zlength ((Znth (row) (players) ((@nil Z))))))) -> ((Znth (col) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col) ((Znth (row) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row) (players) ((@nil Z)))))) ((Znth (row) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ (i <> ((i + 2 ) % ( 3 ) )) ” 
  &&  “ (((i + 2 ) % ( 3 ) ) < 3) ” 
  &&  “ (0 <= ((i + 2 ) % ( 3 ) )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ ((retval <> 0) -> (Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) )) ” 
  &&  “ ((retval = 0) -> ~((Beats (Znth (i) (players) ((@nil Z))) (Znth (((i + 1 ) % ( 3 ) )) (players) ((@nil Z))) ))) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 3) ” 
  &&  “ ((Zlength (players)) = 3) ” 
  &&  “ (Pre (Znth (0) (players) ((@nil Z))) (Znth (1) (players) ((@nil Z))) (Znth (2) (players) ((@nil Z))) ) ” 
  &&  “ ((Zlength (game_mem)) = 3) ” 
  &&  “ forall (row_2: Z) , (((0 <= row_2) /\ (row_2 < 3)) -> (((((Zlength ((Znth (row_2) (players) ((@nil Z))))) < 16) /\ ((Zlength ((Znth (row_2) (game_mem) ((@nil (@option Z)))))) = 16)) /\ forall (col_2: Z) , (((0 <= col_2) /\ (col_2 < (Zlength ((Znth (row_2) (players) ((@nil Z))))))) -> ((Znth (col_2) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some ((Znth (col_2) ((Znth (row_2) (players) ((@nil Z)))) (0))))))) /\ ((Znth ((Zlength ((Znth (row_2) (players) ((@nil Z)))))) ((Znth (row_2) (game_mem) ((@nil (@option Z))))) (None)) = (Some (0))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ~(((Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 1 ) % ( 3 ) )) (players) ((@nil Z))) ) /\ (Beats (Znth (k) (players) ((@nil Z))) (Znth (((k + 2 ) % ( 3 ) )) (players) ((@nil Z))) )))) ”
  &&  (CharArray2.mixed_full g_pre 3 16 game_mem )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.
Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_beats_safety_wit_1 : beats_safety_wit_1.
Axiom proof_of_beats_safety_wit_2 : beats_safety_wit_2.
Axiom proof_of_beats_safety_wit_3 : beats_safety_wit_3.
Axiom proof_of_beats_safety_wit_4 : beats_safety_wit_4.
Axiom proof_of_beats_safety_wit_5 : beats_safety_wit_5.
Axiom proof_of_beats_safety_wit_6 : beats_safety_wit_6.
Axiom proof_of_beats_safety_wit_7 : beats_safety_wit_7.
Axiom proof_of_beats_safety_wit_8 : beats_safety_wit_8.
Axiom proof_of_beats_safety_wit_9 : beats_safety_wit_9.
Axiom proof_of_beats_safety_wit_10 : beats_safety_wit_10.
Axiom proof_of_beats_safety_wit_11 : beats_safety_wit_11.
Axiom proof_of_beats_safety_wit_12 : beats_safety_wit_12.
Axiom proof_of_beats_safety_wit_13 : beats_safety_wit_13.
Axiom proof_of_beats_safety_wit_14 : beats_safety_wit_14.
Axiom proof_of_beats_return_wit_1 : beats_return_wit_1.
Axiom proof_of_beats_return_wit_2 : beats_return_wit_2.
Axiom proof_of_beats_return_wit_3 : beats_return_wit_3.
Axiom proof_of_beats_return_wit_4 : beats_return_wit_4.
Axiom proof_of_beats_return_wit_5 : beats_return_wit_5.
Axiom proof_of_beats_return_wit_6 : beats_return_wit_6.
Axiom proof_of_beats_return_wit_7 : beats_return_wit_7.
Axiom proof_of_beats_partial_solve_wit_1_pure : beats_partial_solve_wit_1_pure.
Axiom proof_of_beats_partial_solve_wit_1 : beats_partial_solve_wit_1.
Axiom proof_of_beats_partial_solve_wit_2_pure : beats_partial_solve_wit_2_pure.
Axiom proof_of_beats_partial_solve_wit_2 : beats_partial_solve_wit_2.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
