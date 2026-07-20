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
Require Import SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function swap_ministers -----*)

Definition swap_ministers_safety_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((( &( "tmp_left" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.full a_pre (2 * n_pre ) flat )
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_ministers_safety_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((( &( "tmp_left" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.full a_pre (2 * n_pre ) flat )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((( &( "tmp_right" ) )) # Int  |->_)
  **  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (((2 * i_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i_pre ) + 1 )) ”
.

Definition swap_ministers_safety_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((( &( "tmp_right" ) )) # Int  |->_)
  **  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_ministers_safety_wit_5 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((( &( "tmp_right" ) )) # Int  |->_)
  **  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_6 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((( &( "tmp_right" ) )) # Int  |->_)
  **  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_ministers_safety_wit_7 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_ministers_safety_wit_8 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_9 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_ministers_safety_wit_10 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_11 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (((2 * i_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i_pre ) + 1 )) ”
.

Definition swap_ministers_safety_wit_12 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ ((2 * i_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i_pre )) ”
.

Definition swap_ministers_safety_wit_13 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_14 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_ministers_safety_wit_15 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (((2 * j_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * j_pre ) + 1 )) ”
.

Definition swap_ministers_safety_wit_16 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_ministers_safety_wit_17 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_18 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_ministers_safety_wit_19 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_ministers_safety_wit_20 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_21 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (((2 * j_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * j_pre ) + 1 )) ”
.

Definition swap_ministers_safety_wit_22 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ ((2 * j_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j_pre )) ”
.

Definition swap_ministers_safety_wit_23 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition swap_ministers_safety_wit_24 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
  **  ((( &( "tmp_right" ) )) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  ((( &( "tmp_left" ) )) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition swap_ministers_return_wit_1 := 
(
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth (((2 * j_pre ) + 1 )) ((Znth ((2 * i_pre ) + 1 ) flat 0)) ((replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))))) )
|--
  “ ((Zlength ((minister_swap (ps) (i_pre) (j_pre)))) = n_pre) ” 
  &&  “ (FlatMinisters (minister_swap_flat (flat) (i_pre) (j_pre)) (minister_swap (ps) (i_pre) (j_pre)) ) ” 
  &&  “ (MinisterHandsBound (minister_swap (ps) (i_pre) (j_pre)) ) ” 
  &&  “ (MinisterPermutation ps (minister_swap (ps) (i_pre) (j_pre)) ) ”
  &&  (IntArray.full a_pre (2 * n_pre ) (minister_swap_flat (flat) (i_pre) (j_pre)) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  TT && emp 
|--
  “ (MinisterPermutation ps (minister_swap (ps) (i_pre) (j_pre)) ) ” 
  &&  “ (MinisterHandsBound (minister_swap (ps) (i_pre) (j_pre)) ) ” 
  &&  “ (FlatMinisters (minister_swap_flat (flat) (i_pre) (j_pre)) (minister_swap (ps) (i_pre) (j_pre)) ) ” 
  &&  “ ((Zlength ((minister_swap (ps) (i_pre) (j_pre)))) = n_pre) ” 
  &&  “ ((replace_Znth (((2 * j_pre ) + 1 )) ((Znth ((2 * i_pre ) + 1 ) flat 0)) ((replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))))) = (minister_swap_flat (flat) (i_pre) (j_pre))) ”
  &&  emp
).

Definition swap_ministers_return_wit_1_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (MinisterPermutation ps (minister_swap (ps) (i_pre) (j_pre)) )
.

Definition swap_ministers_return_wit_1_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (MinisterHandsBound (minister_swap (ps) (i_pre) (j_pre)) )
.

Definition swap_ministers_return_wit_1_split_goal_3 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (FlatMinisters (minister_swap_flat (flat) (i_pre) (j_pre)) (minister_swap (ps) (i_pre) (j_pre)) )
.

Definition swap_ministers_return_wit_1_split_goal_4 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((Zlength ((minister_swap (ps) (i_pre) (j_pre)))) = n_pre)
.

Definition swap_ministers_return_wit_1_split_goal_5 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  ((replace_Znth (((2 * j_pre ) + 1 )) ((Znth ((2 * i_pre ) + 1 ) flat 0)) ((replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))))) = (minister_swap_flat (flat) (i_pre) (j_pre)))
.

Definition swap_ministers_partial_solve_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + ((2 * i_pre ) * sizeof(INT)))) # Int  |-> (Znth (2 * i_pre ) flat 0))
  **  (IntArray.missing_i a_pre (2 * i_pre ) 0 (2 * n_pre ) flat )
.

Definition swap_ministers_partial_solve_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + (((2 * i_pre ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((2 * i_pre ) + 1 ) flat 0))
  **  (IntArray.missing_i a_pre ((2 * i_pre ) + 1 ) 0 (2 * n_pre ) flat )
.

Definition swap_ministers_partial_solve_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + ((2 * j_pre ) * sizeof(INT)))) # Int  |-> (Znth (2 * j_pre ) flat 0))
  **  (IntArray.missing_i a_pre (2 * j_pre ) 0 (2 * n_pre ) flat )
.

Definition swap_ministers_partial_solve_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) flat )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + ((2 * i_pre ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre (2 * i_pre ) 0 (2 * n_pre ) flat )
.

Definition swap_ministers_partial_solve_wit_5 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + (((2 * j_pre ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0))
  **  (IntArray.missing_i a_pre ((2 * j_pre ) + 1 ) 0 (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
.

Definition swap_ministers_partial_solve_wit_6 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + (((2 * i_pre ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre ((2 * i_pre ) + 1 ) 0 (2 * n_pre ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) )
.

Definition swap_ministers_partial_solve_wit_7 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + ((2 * j_pre ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre (2 * j_pre ) 0 (2 * n_pre ) (replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))) )
.

Definition swap_ministers_partial_solve_wit_8 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (a_pre: Z) (ps: (@list minister)) (flat: (@list Z)) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps )) (PreH9 : (MinisterHandsBound ps )) ,
  (IntArray.full a_pre (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (ps)) = n_pre) ” 
  &&  “ (FlatMinisters flat ps ) ” 
  &&  “ (MinisterHandsBound ps ) ”
  &&  (((a_pre + (((2 * j_pre ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i a_pre ((2 * j_pre ) + 1 ) 0 (2 * n_pre ) (replace_Znth ((2 * j_pre )) ((Znth (2 * i_pre ) flat 0)) ((replace_Znth (((2 * i_pre ) + 1 )) ((Znth ((2 * j_pre ) + 1 ) (replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)) 0)) ((replace_Znth ((2 * i_pre )) ((Znth (2 * j_pre ) flat 0)) (flat)))))) )
.

(*----- Function kings_game -----*)

Definition kings_game_safety_wit_1 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.undef_full ans_pre (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kings_game_safety_wit_2 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= k)) (PreH12 : (k <= (2 * n_pre ))) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
  **  (IntArray.undef_seg ans_pre k (2 * n_pre ) )
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition kings_game_safety_wit_3 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= k)) (PreH12 : (k <= (2 * n_pre ))) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
  **  (IntArray.undef_seg ans_pre k (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition kings_game_safety_wit_4 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k < (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  (IntArray.seg ans_pre 0 (k + 1 ) (app ((sublist (0) (k) (input_flat))) ((cons ((Znth k input_flat 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ans_pre (k + 1 ) (2 * n_pre ) )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition kings_game_safety_wit_5 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k >= (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  ((( &( "pass" ) )) # Int  |->_)
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
  **  (IntArray.undef_seg ans_pre k (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kings_game_safety_wit_6 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (pass: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) (PreH10 : (0 <= pass)) (PreH11 : (pass <= (n_pre - 1 ))) (PreH12 : ((Zlength (cur)) = n_pre)) (PreH13 : (FlatMinisters flat_cur cur )) (PreH14 : (MinisterHandsBound cur )) (PreH15 : (MinisterPermutation input cur )) (PreH16 : (BubbleOuterProperty cur n_pre pass )) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition kings_game_safety_wit_7 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (pass: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) (PreH10 : (0 <= pass)) (PreH11 : (pass <= (n_pre - 1 ))) (PreH12 : ((Zlength (cur)) = n_pre)) (PreH13 : (FlatMinisters flat_cur cur )) (PreH14 : (MinisterHandsBound cur )) (PreH15 : (MinisterPermutation input cur )) (PreH16 : (BubbleOuterProperty cur n_pre pass )) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kings_game_safety_wit_8 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (pass: Z) (PreH1 : (pass < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass <= (n_pre - 1 ))) (PreH13 : ((Zlength (cur)) = n_pre)) (PreH14 : (FlatMinisters flat_cur cur )) (PreH15 : (MinisterHandsBound cur )) (PreH16 : (MinisterPermutation input cur )) (PreH17 : (BubbleOuterProperty cur n_pre pass )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kings_game_safety_wit_9 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) (PreH10 : (0 <= pass)) (PreH11 : (pass < (n_pre - 1 ))) (PreH12 : (0 <= j)) (PreH13 : (j <= ((n_pre - 1 ) - pass ))) (PreH14 : ((Zlength (cur)) = n_pre)) (PreH15 : (FlatMinisters flat_cur cur )) (PreH16 : (MinisterHandsBound cur )) (PreH17 : (MinisterPermutation input cur )) (PreH18 : (BubbleOuterProperty cur n_pre pass )) (PreH19 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ (((n_pre - 1 ) - pass ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre - 1 ) - pass )) ”
.

Definition kings_game_safety_wit_10 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) (PreH10 : (0 <= pass)) (PreH11 : (pass < (n_pre - 1 ))) (PreH12 : (0 <= j)) (PreH13 : (j <= ((n_pre - 1 ) - pass ))) (PreH14 : ((Zlength (cur)) = n_pre)) (PreH15 : (FlatMinisters flat_cur cur )) (PreH16 : (MinisterHandsBound cur )) (PreH17 : (MinisterPermutation input cur )) (PreH18 : (BubbleOuterProperty cur n_pre pass )) (PreH19 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition kings_game_safety_wit_11 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) (PreH10 : (0 <= pass)) (PreH11 : (pass < (n_pre - 1 ))) (PreH12 : (0 <= j)) (PreH13 : (j <= ((n_pre - 1 ) - pass ))) (PreH14 : ((Zlength (cur)) = n_pre)) (PreH15 : (FlatMinisters flat_cur cur )) (PreH16 : (MinisterHandsBound cur )) (PreH17 : (MinisterPermutation input cur )) (PreH18 : (BubbleOuterProperty cur n_pre pass )) (PreH19 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kings_game_safety_wit_12 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "left1" ) )) # Int  |->_)
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ ((2 * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j )) ”
.

Definition kings_game_safety_wit_13 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "left1" ) )) # Int  |->_)
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition kings_game_safety_wit_14 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right1" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((2 * j ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * j ) + 1 )) ”
.

Definition kings_game_safety_wit_15 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right1" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((2 * j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * j )) ”
.

Definition kings_game_safety_wit_16 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right1" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition kings_game_safety_wit_17 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right1" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kings_game_safety_wit_18 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "left2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((2 * (j + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * (j + 1 ) )) ”
.

Definition kings_game_safety_wit_19 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "left2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition kings_game_safety_wit_20 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "left2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition kings_game_safety_wit_21 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "left2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kings_game_safety_wit_22 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((2 * (j + 1 ) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * (j + 1 ) ) + 1 )) ”
.

Definition kings_game_safety_wit_23 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((2 * (j + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * (j + 1 ) )) ”
.

Definition kings_game_safety_wit_24 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition kings_game_safety_wit_25 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition kings_game_safety_wit_26 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kings_game_safety_wit_27 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "right2" ) )) # Int  |->_)
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kings_game_safety_wit_28 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) )) ”
) \/
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) )) ”
).

Definition kings_game_safety_wit_28_split_goal_1 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ) <= INT_MAX) ”
.

Definition kings_game_safety_wit_28_split_goal_2 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((INT_MIN) <= ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) )) ”
.

Definition kings_game_safety_wit_29 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) )) ”
) \/
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) )) ”
).

Definition kings_game_safety_wit_29_split_goal_1 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) <= INT_MAX) ”
.

Definition kings_game_safety_wit_29_split_goal_2 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((INT_MIN) <= ((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) )) ”
.

Definition kings_game_safety_wit_30 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ))) (PreH2 : (j < ((n_pre - 1 ) - pass ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= pass)) (PreH13 : (pass < (n_pre - 1 ))) (PreH14 : (0 <= j)) (PreH15 : (j <= ((n_pre - 1 ) - pass ))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur )) (PreH18 : (MinisterHandsBound cur )) (PreH19 : (MinisterPermutation input cur )) (PreH20 : (BubbleOuterProperty cur n_pre pass )) (PreH21 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition kings_game_safety_wit_31 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ))) (PreH2 : (j < ((n_pre - 1 ) - pass ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= pass)) (PreH13 : (pass < (n_pre - 1 ))) (PreH14 : (0 <= j)) (PreH15 : (j <= ((n_pre - 1 ) - pass ))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur )) (PreH18 : (MinisterHandsBound cur )) (PreH19 : (MinisterPermutation input cur )) (PreH20 : (BubbleOuterProperty cur n_pre pass )) (PreH21 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kings_game_safety_wit_32 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : ((Zlength ((minister_swap (cur) (j) ((j + 1 ))))) = n_pre)) (PreH2 : (FlatMinisters (minister_swap_flat (flat_cur) (j) ((j + 1 ))) (minister_swap (cur) (j) ((j + 1 ))) )) (PreH3 : (MinisterHandsBound (minister_swap (cur) (j) ((j + 1 ))) )) (PreH4 : (MinisterPermutation cur (minister_swap (cur) (j) ((j + 1 ))) )) (PreH5 : (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ))) (PreH6 : (j < ((n_pre - 1 ) - pass ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 8)) (PreH9 : (1 <= king_left_pre)) (PreH10 : (king_left_pre <= 10)) (PreH11 : (1 <= king_right_pre)) (PreH12 : (king_right_pre <= 10)) (PreH13 : ((Zlength (input)) = n_pre)) (PreH14 : (FlatMinisters input_flat input )) (PreH15 : (MinisterHandsBound input )) (PreH16 : (0 <= pass)) (PreH17 : (pass < (n_pre - 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= ((n_pre - 1 ) - pass ))) (PreH20 : ((Zlength (cur)) = n_pre)) (PreH21 : (FlatMinisters flat_cur cur )) (PreH22 : (MinisterHandsBound cur )) (PreH23 : (MinisterPermutation input cur )) (PreH24 : (BubbleOuterProperty cur n_pre pass )) (PreH25 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) (minister_swap_flat (flat_cur) (j) ((j + 1 ))) )
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition kings_game_safety_wit_33 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) <= ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ))) (PreH2 : (j < ((n_pre - 1 ) - pass ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= pass)) (PreH13 : (pass < (n_pre - 1 ))) (PreH14 : (0 <= j)) (PreH15 : (j <= ((n_pre - 1 ) - pass ))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur )) (PreH18 : (MinisterHandsBound cur )) (PreH19 : (MinisterPermutation input cur )) (PreH20 : (BubbleOuterProperty cur n_pre pass )) (PreH21 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition kings_game_safety_wit_34 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j >= ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ ((pass + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pass + 1 )) ”
.

Definition kings_game_entail_wit_1 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.undef_full ans_pre (2 * n_pre ) )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (input_flat)) = (2 * n_pre )) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (2 * n_pre )) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 0 (sublist (0) (0) (input_flat)) )
  **  (IntArray.undef_seg ans_pre 0 (2 * n_pre ) )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) ,
  TT && emp 
|--
  “ ((Zlength (input_flat)) = (2 * n_pre )) ” 
  &&  “ ((sublist (0) (0) (input_flat)) = (@nil Z)) ”
  &&  emp
).

Definition kings_game_entail_wit_1_split_goal_1 := 
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) ,
  ((Zlength (input_flat)) = (2 * n_pre ))
.

Definition kings_game_entail_wit_1_split_goal_2 := 
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input )) (PreH9 : (MinisterHandsBound input )) ,
  ((sublist (0) (0) (input_flat)) = (@nil Z))
.

Definition kings_game_entail_wit_2 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k < (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  (IntArray.seg ans_pre 0 (k + 1 ) (app ((sublist (0) (k) (input_flat))) ((cons ((Znth k input_flat 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ans_pre (k + 1 ) (2 * n_pre ) )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (input_flat)) = (2 * n_pre )) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (2 * n_pre )) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 (k + 1 ) (sublist (0) ((k + 1 )) (input_flat)) )
  **  (IntArray.undef_seg ans_pre (k + 1 ) (2 * n_pre ) )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k < (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (k) (input_flat))) ((cons ((Znth k input_flat 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) (input_flat))) ”
  &&  emp
).

Definition kings_game_entail_wit_2_split_goal_1 := 
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k < (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  ((app ((sublist (0) (k) (input_flat))) ((cons ((Znth k input_flat 0)) ((@nil Z))))) = (sublist (0) ((k + 1 )) (input_flat)))
.

Definition kings_game_entail_wit_3 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k >= (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
  **  (IntArray.undef_seg ans_pre k (2 * n_pre ) )
|--
  EX (flat_cur: (@list Z))  (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre 0 ) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k >= (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  TT && emp 
|--
  EX (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters (sublist (0) (k) (input_flat)) cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre 0 ) ”
  &&  emp
).

Definition kings_game_entail_wit_4 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (pass: Z) (PreH1 : (pass < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass <= (n_pre - 1 ))) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (FlatMinisters flat_cur_2 cur_2 )) (PreH15 : (MinisterHandsBound cur_2 )) (PreH16 : (MinisterPermutation input cur_2 )) (PreH17 : (BubbleOuterProperty cur_2 n_pre pass )) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur_2 )
|--
  EX (flat_cur: (@list Z))  (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass 0 ) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (pass: Z) (PreH1 : (pass < (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass <= (n_pre - 1 ))) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (FlatMinisters flat_cur_2 cur_2 )) (PreH15 : (MinisterHandsBound cur_2 )) (PreH16 : (MinisterPermutation input cur_2 )) (PreH17 : (BubbleOuterProperty cur_2 n_pre pass )) ,
  TT && emp 
|--
  EX (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur_2 cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass 0 ) ”
  &&  emp
).

Definition kings_game_entail_wit_5_1 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (j: Z) (pass: Z) (PreH1 : ((Zlength ((minister_swap (cur_2) (j) ((j + 1 ))))) = n_pre)) (PreH2 : (FlatMinisters (minister_swap_flat (flat_cur_2) (j) ((j + 1 ))) (minister_swap (cur_2) (j) ((j + 1 ))) )) (PreH3 : (MinisterHandsBound (minister_swap (cur_2) (j) ((j + 1 ))) )) (PreH4 : (MinisterPermutation cur_2 (minister_swap (cur_2) (j) ((j + 1 ))) )) (PreH5 : (((Znth (2 * j ) flat_cur_2 0) * (Znth ((2 * j ) + 1 ) flat_cur_2 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur_2 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur_2 0) ))) (PreH6 : (j < ((n_pre - 1 ) - pass ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 8)) (PreH9 : (1 <= king_left_pre)) (PreH10 : (king_left_pre <= 10)) (PreH11 : (1 <= king_right_pre)) (PreH12 : (king_right_pre <= 10)) (PreH13 : ((Zlength (input)) = n_pre)) (PreH14 : (FlatMinisters input_flat input )) (PreH15 : (MinisterHandsBound input )) (PreH16 : (0 <= pass)) (PreH17 : (pass < (n_pre - 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= ((n_pre - 1 ) - pass ))) (PreH20 : ((Zlength (cur_2)) = n_pre)) (PreH21 : (FlatMinisters flat_cur_2 cur_2 )) (PreH22 : (MinisterHandsBound cur_2 )) (PreH23 : (MinisterPermutation input cur_2 )) (PreH24 : (BubbleOuterProperty cur_2 n_pre pass )) (PreH25 : (BubbleScanProperty cur_2 n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) (minister_swap_flat (flat_cur_2) (j) ((j + 1 ))) )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  EX (flat_cur: (@list Z))  (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass (j + 1 ) ) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (j: Z) (pass: Z) (PreH1 : ((Zlength ((minister_swap (cur_2) (j) ((j + 1 ))))) = n_pre)) (PreH2 : (FlatMinisters (minister_swap_flat (flat_cur_2) (j) ((j + 1 ))) (minister_swap (cur_2) (j) ((j + 1 ))) )) (PreH3 : (MinisterHandsBound (minister_swap (cur_2) (j) ((j + 1 ))) )) (PreH4 : (MinisterPermutation cur_2 (minister_swap (cur_2) (j) ((j + 1 ))) )) (PreH5 : (((Znth (2 * j ) flat_cur_2 0) * (Znth ((2 * j ) + 1 ) flat_cur_2 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur_2 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur_2 0) ))) (PreH6 : (j < ((n_pre - 1 ) - pass ))) (PreH7 : (1 <= n_pre)) (PreH8 : (n_pre <= 8)) (PreH9 : (1 <= king_left_pre)) (PreH10 : (king_left_pre <= 10)) (PreH11 : (1 <= king_right_pre)) (PreH12 : (king_right_pre <= 10)) (PreH13 : ((Zlength (input)) = n_pre)) (PreH14 : (FlatMinisters input_flat input )) (PreH15 : (MinisterHandsBound input )) (PreH16 : (0 <= pass)) (PreH17 : (pass < (n_pre - 1 ))) (PreH18 : (0 <= j)) (PreH19 : (j <= ((n_pre - 1 ) - pass ))) (PreH20 : ((Zlength (cur_2)) = n_pre)) (PreH21 : (FlatMinisters flat_cur_2 cur_2 )) (PreH22 : (MinisterHandsBound cur_2 )) (PreH23 : (MinisterPermutation input cur_2 )) (PreH24 : (BubbleOuterProperty cur_2 n_pre pass )) (PreH25 : (BubbleScanProperty cur_2 n_pre pass j )) ,
  TT && emp 
|--
  EX (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters (minister_swap_flat (flat_cur_2) (j) ((j + 1 ))) cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass (j + 1 ) ) ”
  &&  emp
).

Definition kings_game_entail_wit_5_2 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (j: Z) (pass: Z) (PreH1 : (((Znth (2 * j ) flat_cur_2 0) * (Znth ((2 * j ) + 1 ) flat_cur_2 0) ) <= ((Znth (2 * (j + 1 ) ) flat_cur_2 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur_2 0) ))) (PreH2 : (j < ((n_pre - 1 ) - pass ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= pass)) (PreH13 : (pass < (n_pre - 1 ))) (PreH14 : (0 <= j)) (PreH15 : (j <= ((n_pre - 1 ) - pass ))) (PreH16 : ((Zlength (cur_2)) = n_pre)) (PreH17 : (FlatMinisters flat_cur_2 cur_2 )) (PreH18 : (MinisterHandsBound cur_2 )) (PreH19 : (MinisterPermutation input cur_2 )) (PreH20 : (BubbleOuterProperty cur_2 n_pre pass )) (PreH21 : (BubbleScanProperty cur_2 n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur_2 )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  EX (flat_cur: (@list Z))  (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass (j + 1 ) ) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (j: Z) (pass: Z) (PreH1 : (((Znth (2 * j ) flat_cur_2 0) * (Znth ((2 * j ) + 1 ) flat_cur_2 0) ) <= ((Znth (2 * (j + 1 ) ) flat_cur_2 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur_2 0) ))) (PreH2 : (j < ((n_pre - 1 ) - pass ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= pass)) (PreH13 : (pass < (n_pre - 1 ))) (PreH14 : (0 <= j)) (PreH15 : (j <= ((n_pre - 1 ) - pass ))) (PreH16 : ((Zlength (cur_2)) = n_pre)) (PreH17 : (FlatMinisters flat_cur_2 cur_2 )) (PreH18 : (MinisterHandsBound cur_2 )) (PreH19 : (MinisterPermutation input cur_2 )) (PreH20 : (BubbleOuterProperty cur_2 n_pre pass )) (PreH21 : (BubbleScanProperty cur_2 n_pre pass j )) ,
  TT && emp 
|--
  EX (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur_2 cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass (j + 1 ) ) ”
  &&  emp
).

Definition kings_game_entail_wit_6 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j >= ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur_2)) = n_pre)) (PreH16 : (FlatMinisters flat_cur_2 cur_2 )) (PreH17 : (MinisterHandsBound cur_2 )) (PreH18 : (MinisterPermutation input cur_2 )) (PreH19 : (BubbleOuterProperty cur_2 n_pre pass )) (PreH20 : (BubbleScanProperty cur_2 n_pre pass j )) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur_2 )
|--
  EX (flat_cur: (@list Z))  (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= (pass + 1 )) ” 
  &&  “ ((pass + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre (pass + 1 ) ) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur_2: (@list Z)) (cur_2: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j >= ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur_2)) = n_pre)) (PreH16 : (FlatMinisters flat_cur_2 cur_2 )) (PreH17 : (MinisterHandsBound cur_2 )) (PreH18 : (MinisterPermutation input cur_2 )) (PreH19 : (BubbleOuterProperty cur_2 n_pre pass )) (PreH20 : (BubbleScanProperty cur_2 n_pre pass j )) ,
  TT && emp 
|--
  EX (cur: (@list minister)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= (pass + 1 )) ” 
  &&  “ ((pass + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur_2 cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre (pass + 1 ) ) ”
  &&  emp
).

Definition kings_game_return_wit_1 := 
(
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (pass: Z) (PreH1 : (pass >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass <= (n_pre - 1 ))) (PreH13 : ((Zlength (cur)) = n_pre)) (PreH14 : (FlatMinisters flat_cur cur )) (PreH15 : (MinisterHandsBound cur )) (PreH16 : (MinisterPermutation input cur )) (PreH17 : (BubbleOuterProperty cur n_pre pass )) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  EX (output_flat: (@list Z))  (output: (@list minister)) ,
  “ ((Zlength (output)) = n_pre) ” 
  &&  “ (FlatMinisters output_flat output ) ” 
  &&  “ (MinisterHandsBound output ) ” 
  &&  “ (KingsGameResult input king_left_pre output ) ”
  &&  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) output_flat )
) \/
(
forall (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (pass: Z) (PreH1 : (pass >= (n_pre - 1 ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass <= (n_pre - 1 ))) (PreH13 : ((Zlength (cur)) = n_pre)) (PreH14 : (FlatMinisters flat_cur cur )) (PreH15 : (MinisterHandsBound cur )) (PreH16 : (MinisterPermutation input cur )) (PreH17 : (BubbleOuterProperty cur n_pre pass )) ,
  TT && emp 
|--
  EX (output: (@list minister)) ,
  “ ((Zlength (output)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur output ) ” 
  &&  “ (MinisterHandsBound output ) ” 
  &&  “ (KingsGameResult input king_left_pre output ) ”
  &&  emp
).

Definition kings_game_partial_solve_wit_1 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k < (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
  **  (IntArray.undef_seg ans_pre k (2 * n_pre ) )
|--
  “ (k < (2 * n_pre )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (input_flat)) = (2 * n_pre )) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (2 * n_pre )) ”
  &&  (((ministers_pre + (k * sizeof(INT)))) # Int  |-> (Znth k input_flat 0))
  **  (IntArray.missing_i ministers_pre k 0 (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
  **  (IntArray.undef_seg ans_pre k (2 * n_pre ) )
.

Definition kings_game_partial_solve_wit_2 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (k: Z) (PreH1 : (k < (2 * n_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre ))) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= k)) (PreH13 : (k <= (2 * n_pre ))) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
  **  (IntArray.undef_seg ans_pre k (2 * n_pre ) )
|--
  “ (k < (2 * n_pre )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ ((Zlength (input_flat)) = (2 * n_pre )) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (2 * n_pre )) ”
  &&  (((ans_pre + (k * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ans_pre (k + 1 ) (2 * n_pre ) )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.seg ans_pre 0 k (sublist (0) (k) (input_flat)) )
.

Definition kings_game_partial_solve_wit_3 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
  **  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
|--
  “ (j < ((n_pre - 1 ) - pass )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass j ) ”
  &&  (((ans_pre + ((2 * j ) * sizeof(INT)))) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  (IntArray.missing_i ans_pre (2 * j ) 0 (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
.

Definition kings_game_partial_solve_wit_4 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (j < ((n_pre - 1 ) - pass )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass j ) ”
  &&  (((ans_pre + (((2 * j ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  (IntArray.missing_i ans_pre ((2 * j ) + 1 ) 0 (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
.

Definition kings_game_partial_solve_wit_5 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (j < ((n_pre - 1 ) - pass )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass j ) ”
  &&  (((ans_pre + ((2 * (j + 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  (IntArray.missing_i ans_pre (2 * (j + 1 ) ) 0 (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
.

Definition kings_game_partial_solve_wit_6 := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (j < ((n_pre - 1 ) - pass ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input )) (PreH10 : (MinisterHandsBound input )) (PreH11 : (0 <= pass)) (PreH12 : (pass < (n_pre - 1 ))) (PreH13 : (0 <= j)) (PreH14 : (j <= ((n_pre - 1 ) - pass ))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur )) (PreH17 : (MinisterHandsBound cur )) (PreH18 : (MinisterPermutation input cur )) (PreH19 : (BubbleOuterProperty cur n_pre pass )) (PreH20 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (j < ((n_pre - 1 ) - pass )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass j ) ”
  &&  (((ans_pre + (((2 * (j + 1 ) ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  (IntArray.missing_i ans_pre ((2 * (j + 1 ) ) + 1 ) 0 (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
.

Definition kings_game_partial_solve_wit_7_pure := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ))) (PreH2 : (j < ((n_pre - 1 ) - pass ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= pass)) (PreH13 : (pass < (n_pre - 1 ))) (PreH14 : (0 <= j)) (PreH15 : (j <= ((n_pre - 1 ) - pass ))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur )) (PreH18 : (MinisterHandsBound cur )) (PreH19 : (MinisterPermutation input cur )) (PreH20 : (BubbleOuterProperty cur n_pre pass )) (PreH21 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  ((( &( "right2" ) )) # Int  |-> (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0))
  **  ((( &( "left2" ) )) # Int  |-> (Znth (2 * (j + 1 ) ) flat_cur 0))
  **  ((( &( "right1" ) )) # Int  |-> (Znth ((2 * j ) + 1 ) flat_cur 0))
  **  ((( &( "left1" ) )) # Int  |-> (Znth (2 * j ) flat_cur 0))
  **  ((( &( "ministers" ) )) # Ptr  |-> ministers_pre)
  **  ((( &( "ans" ) )) # Ptr  |-> ans_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "king_left" ) )) # Int  |-> king_left_pre)
  **  ((( &( "king_right" ) )) # Int  |-> king_right_pre)
  **  ((( &( "pass" ) )) # Int  |-> pass)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ”
.

Definition kings_game_partial_solve_wit_7_aux := 
forall (ans_pre: Z) (king_right_pre: Z) (king_left_pre: Z) (n_pre: Z) (ministers_pre: Z) (input: (@list minister)) (input_flat: (@list Z)) (flat_cur: (@list Z)) (cur: (@list minister)) (j: Z) (pass: Z) (PreH1 : (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) ))) (PreH2 : (j < ((n_pre - 1 ) - pass ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input )) (PreH11 : (MinisterHandsBound input )) (PreH12 : (0 <= pass)) (PreH13 : (pass < (n_pre - 1 ))) (PreH14 : (0 <= j)) (PreH15 : (j <= ((n_pre - 1 ) - pass ))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur )) (PreH18 : (MinisterHandsBound cur )) (PreH19 : (MinisterPermutation input cur )) (PreH20 : (BubbleOuterProperty cur n_pre pass )) (PreH21 : (BubbleScanProperty cur n_pre pass j )) ,
  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
|--
  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (((Znth (2 * j ) flat_cur 0) * (Znth ((2 * j ) + 1 ) flat_cur 0) ) > ((Znth (2 * (j + 1 ) ) flat_cur 0) * (Znth ((2 * (j + 1 ) ) + 1 ) flat_cur 0) )) ” 
  &&  “ (j < ((n_pre - 1 ) - pass )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= king_left_pre) ” 
  &&  “ (king_left_pre <= 10) ” 
  &&  “ (1 <= king_right_pre) ” 
  &&  “ (king_right_pre <= 10) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (FlatMinisters input_flat input ) ” 
  &&  “ (MinisterHandsBound input ) ” 
  &&  “ (0 <= pass) ” 
  &&  “ (pass < (n_pre - 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= ((n_pre - 1 ) - pass )) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (FlatMinisters flat_cur cur ) ” 
  &&  “ (MinisterHandsBound cur ) ” 
  &&  “ (MinisterPermutation input cur ) ” 
  &&  “ (BubbleOuterProperty cur n_pre pass ) ” 
  &&  “ (BubbleScanProperty cur n_pre pass j ) ”
  &&  (IntArray.full ans_pre (2 * n_pre ) flat_cur )
  **  (IntArray.full ministers_pre (2 * n_pre ) input_flat )
.

Definition kings_game_partial_solve_wit_7 := kings_game_partial_solve_wit_7_pure -> kings_game_partial_solve_wit_7_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_swap_ministers_safety_wit_1 : swap_ministers_safety_wit_1.
Axiom proof_of_swap_ministers_safety_wit_2 : swap_ministers_safety_wit_2.
Axiom proof_of_swap_ministers_safety_wit_3 : swap_ministers_safety_wit_3.
Axiom proof_of_swap_ministers_safety_wit_4 : swap_ministers_safety_wit_4.
Axiom proof_of_swap_ministers_safety_wit_5 : swap_ministers_safety_wit_5.
Axiom proof_of_swap_ministers_safety_wit_6 : swap_ministers_safety_wit_6.
Axiom proof_of_swap_ministers_safety_wit_7 : swap_ministers_safety_wit_7.
Axiom proof_of_swap_ministers_safety_wit_8 : swap_ministers_safety_wit_8.
Axiom proof_of_swap_ministers_safety_wit_9 : swap_ministers_safety_wit_9.
Axiom proof_of_swap_ministers_safety_wit_10 : swap_ministers_safety_wit_10.
Axiom proof_of_swap_ministers_safety_wit_11 : swap_ministers_safety_wit_11.
Axiom proof_of_swap_ministers_safety_wit_12 : swap_ministers_safety_wit_12.
Axiom proof_of_swap_ministers_safety_wit_13 : swap_ministers_safety_wit_13.
Axiom proof_of_swap_ministers_safety_wit_14 : swap_ministers_safety_wit_14.
Axiom proof_of_swap_ministers_safety_wit_15 : swap_ministers_safety_wit_15.
Axiom proof_of_swap_ministers_safety_wit_16 : swap_ministers_safety_wit_16.
Axiom proof_of_swap_ministers_safety_wit_17 : swap_ministers_safety_wit_17.
Axiom proof_of_swap_ministers_safety_wit_18 : swap_ministers_safety_wit_18.
Axiom proof_of_swap_ministers_safety_wit_19 : swap_ministers_safety_wit_19.
Axiom proof_of_swap_ministers_safety_wit_20 : swap_ministers_safety_wit_20.
Axiom proof_of_swap_ministers_safety_wit_21 : swap_ministers_safety_wit_21.
Axiom proof_of_swap_ministers_safety_wit_22 : swap_ministers_safety_wit_22.
Axiom proof_of_swap_ministers_safety_wit_23 : swap_ministers_safety_wit_23.
Axiom proof_of_swap_ministers_safety_wit_24 : swap_ministers_safety_wit_24.
Axiom proof_of_swap_ministers_return_wit_1 : swap_ministers_return_wit_1.
Axiom proof_of_swap_ministers_partial_solve_wit_1 : swap_ministers_partial_solve_wit_1.
Axiom proof_of_swap_ministers_partial_solve_wit_2 : swap_ministers_partial_solve_wit_2.
Axiom proof_of_swap_ministers_partial_solve_wit_3 : swap_ministers_partial_solve_wit_3.
Axiom proof_of_swap_ministers_partial_solve_wit_4 : swap_ministers_partial_solve_wit_4.
Axiom proof_of_swap_ministers_partial_solve_wit_5 : swap_ministers_partial_solve_wit_5.
Axiom proof_of_swap_ministers_partial_solve_wit_6 : swap_ministers_partial_solve_wit_6.
Axiom proof_of_swap_ministers_partial_solve_wit_7 : swap_ministers_partial_solve_wit_7.
Axiom proof_of_swap_ministers_partial_solve_wit_8 : swap_ministers_partial_solve_wit_8.
Axiom proof_of_kings_game_safety_wit_1 : kings_game_safety_wit_1.
Axiom proof_of_kings_game_safety_wit_2 : kings_game_safety_wit_2.
Axiom proof_of_kings_game_safety_wit_3 : kings_game_safety_wit_3.
Axiom proof_of_kings_game_safety_wit_4 : kings_game_safety_wit_4.
Axiom proof_of_kings_game_safety_wit_5 : kings_game_safety_wit_5.
Axiom proof_of_kings_game_safety_wit_6 : kings_game_safety_wit_6.
Axiom proof_of_kings_game_safety_wit_7 : kings_game_safety_wit_7.
Axiom proof_of_kings_game_safety_wit_8 : kings_game_safety_wit_8.
Axiom proof_of_kings_game_safety_wit_9 : kings_game_safety_wit_9.
Axiom proof_of_kings_game_safety_wit_10 : kings_game_safety_wit_10.
Axiom proof_of_kings_game_safety_wit_11 : kings_game_safety_wit_11.
Axiom proof_of_kings_game_safety_wit_12 : kings_game_safety_wit_12.
Axiom proof_of_kings_game_safety_wit_13 : kings_game_safety_wit_13.
Axiom proof_of_kings_game_safety_wit_14 : kings_game_safety_wit_14.
Axiom proof_of_kings_game_safety_wit_15 : kings_game_safety_wit_15.
Axiom proof_of_kings_game_safety_wit_16 : kings_game_safety_wit_16.
Axiom proof_of_kings_game_safety_wit_17 : kings_game_safety_wit_17.
Axiom proof_of_kings_game_safety_wit_18 : kings_game_safety_wit_18.
Axiom proof_of_kings_game_safety_wit_19 : kings_game_safety_wit_19.
Axiom proof_of_kings_game_safety_wit_20 : kings_game_safety_wit_20.
Axiom proof_of_kings_game_safety_wit_21 : kings_game_safety_wit_21.
Axiom proof_of_kings_game_safety_wit_22 : kings_game_safety_wit_22.
Axiom proof_of_kings_game_safety_wit_23 : kings_game_safety_wit_23.
Axiom proof_of_kings_game_safety_wit_24 : kings_game_safety_wit_24.
Axiom proof_of_kings_game_safety_wit_25 : kings_game_safety_wit_25.
Axiom proof_of_kings_game_safety_wit_26 : kings_game_safety_wit_26.
Axiom proof_of_kings_game_safety_wit_27 : kings_game_safety_wit_27.
Axiom proof_of_kings_game_safety_wit_28 : kings_game_safety_wit_28.
Axiom proof_of_kings_game_safety_wit_29 : kings_game_safety_wit_29.
Axiom proof_of_kings_game_safety_wit_30 : kings_game_safety_wit_30.
Axiom proof_of_kings_game_safety_wit_31 : kings_game_safety_wit_31.
Axiom proof_of_kings_game_safety_wit_32 : kings_game_safety_wit_32.
Axiom proof_of_kings_game_safety_wit_33 : kings_game_safety_wit_33.
Axiom proof_of_kings_game_safety_wit_34 : kings_game_safety_wit_34.
Axiom proof_of_kings_game_entail_wit_1 : kings_game_entail_wit_1.
Axiom proof_of_kings_game_entail_wit_2 : kings_game_entail_wit_2.
Axiom proof_of_kings_game_entail_wit_3 : kings_game_entail_wit_3.
Axiom proof_of_kings_game_entail_wit_4 : kings_game_entail_wit_4.
Axiom proof_of_kings_game_entail_wit_5_1 : kings_game_entail_wit_5_1.
Axiom proof_of_kings_game_entail_wit_5_2 : kings_game_entail_wit_5_2.
Axiom proof_of_kings_game_entail_wit_6 : kings_game_entail_wit_6.
Axiom proof_of_kings_game_return_wit_1 : kings_game_return_wit_1.
Axiom proof_of_kings_game_partial_solve_wit_1 : kings_game_partial_solve_wit_1.
Axiom proof_of_kings_game_partial_solve_wit_2 : kings_game_partial_solve_wit_2.
Axiom proof_of_kings_game_partial_solve_wit_3 : kings_game_partial_solve_wit_3.
Axiom proof_of_kings_game_partial_solve_wit_4 : kings_game_partial_solve_wit_4.
Axiom proof_of_kings_game_partial_solve_wit_5 : kings_game_partial_solve_wit_5.
Axiom proof_of_kings_game_partial_solve_wit_6 : kings_game_partial_solve_wit_6.
Axiom proof_of_kings_game_partial_solve_wit_7_pure : kings_game_partial_solve_wit_7_pure.
Axiom proof_of_kings_game_partial_solve_wit_7 : kings_game_partial_solve_wit_7.

End VC_Correct.
