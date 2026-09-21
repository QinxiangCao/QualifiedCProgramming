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
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope monad.
Require Import SimpleC.EE.LLM_bench.Algorithms.Kruskal.kruskal_union_find_lib.
Require Import ListLib.Base.Positional.
From SumLib Require Import ZRange.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function swap_int -----*)

Definition swap_int_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (y_neq: Z) (x_neq: Z) ,
  ((a_pre) # Int  |-> y_neq)
  **  ((b_pre) # Int  |-> x_neq)
|--
  ((a_pre) # Int  |-> y_neq)
  **  ((b_pre) # Int  |-> x_neq)
.

(*----- Function swap_edge -----*)

Definition swap_edge_entail_wit_1 := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre < j_pre)) (PreH2 : (i_pre <> j_pre)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < n)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < n)) (PreH7 : ((Zlength (l_u)) = n)) (PreH8 : ((Zlength (l_v)) = n)) (PreH9 : ((Zlength (l_w)) = n)) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre < j_pre)) (PreH2 : (i_pre <> j_pre)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < n)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < n)) (PreH7 : ((Zlength (l_u)) = n)) (PreH8 : ((Zlength (l_v)) = n)) (PreH9 : ((Zlength (l_w)) = n)) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
).

Definition swap_edge_entail_wit_1_split_goal_spatial := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre < j_pre)) (PreH2 : (i_pre <> j_pre)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < n)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < n)) (PreH7 : ((Zlength (l_u)) = n)) (PreH8 : ((Zlength (l_v)) = n)) (PreH9 : ((Zlength (l_w)) = n)) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
.

Definition swap_edge_entail_wit_2 := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre >= j_pre)) (PreH2 : (i_pre <> j_pre)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < n)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < n)) (PreH7 : ((Zlength (l_u)) = n)) (PreH8 : ((Zlength (l_v)) = n)) (PreH9 : ((Zlength (l_w)) = n)) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  “ (0 <= j_pre) ” 
  &&  “ (j_pre < i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre >= j_pre)) (PreH2 : (i_pre <> j_pre)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < n)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < n)) (PreH7 : ((Zlength (l_u)) = n)) (PreH8 : ((Zlength (l_v)) = n)) (PreH9 : ((Zlength (l_w)) = n)) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
).

Definition swap_edge_entail_wit_2_split_goal_spatial := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre >= j_pre)) (PreH2 : (i_pre <> j_pre)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < n)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < n)) (PreH7 : ((Zlength (l_u)) = n)) (PreH8 : ((Zlength (l_v)) = n)) (PreH9 : ((Zlength (l_w)) = n)) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
.

Definition swap_edge_return_wit_1 := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg w_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_w 0)) ((sublist (j_pre) (n) (l_w)))) )
  **  (IntArray.full w_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_w 0)) ((sublist (0) (j_pre) (l_w)))) )
  **  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
|--
  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (IntArray.full u_pre n (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((replace_Znth (i_pre) ((Znth j_pre l_u 0)) (l_u)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((replace_Znth (i_pre) ((Znth j_pre l_v 0)) (l_v)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((replace_Znth (i_pre) ((Znth j_pre l_w 0)) (l_w)))) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg w_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_w 0)) ((sublist (j_pre) (n) (l_w)))) )
  **  (IntArray.full w_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_w 0)) ((sublist (0) (j_pre) (l_w)))) )
  **  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
|--
  (IntArray.full u_pre n (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((replace_Znth (i_pre) ((Znth j_pre l_u 0)) (l_u)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((replace_Znth (i_pre) ((Znth j_pre l_v 0)) (l_v)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((replace_Znth (i_pre) ((Znth j_pre l_w 0)) (l_w)))) )
).

Definition swap_edge_return_wit_1_split_goal_spatial := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg w_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_w 0)) ((sublist (j_pre) (n) (l_w)))) )
  **  (IntArray.full w_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_w 0)) ((sublist (0) (j_pre) (l_w)))) )
  **  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
|--
  (IntArray.full u_pre n (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((replace_Znth (i_pre) ((Znth j_pre l_u 0)) (l_u)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((replace_Znth (i_pre) ((Znth j_pre l_v 0)) (l_v)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((replace_Znth (i_pre) ((Znth j_pre l_w 0)) (l_w)))) )
.

Definition swap_edge_return_wit_2 := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg w_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_w 0)) ((sublist (i_pre) (n) (l_w)))) )
  **  (IntArray.full w_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((sublist (0) (i_pre) (l_w)))) )
  **  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
|--
  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (IntArray.full u_pre n (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((replace_Znth (i_pre) ((Znth j_pre l_u 0)) (l_u)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((replace_Znth (i_pre) ((Znth j_pre l_v 0)) (l_v)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((replace_Znth (i_pre) ((Znth j_pre l_w 0)) (l_w)))) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg w_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_w 0)) ((sublist (i_pre) (n) (l_w)))) )
  **  (IntArray.full w_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((sublist (0) (i_pre) (l_w)))) )
  **  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
|--
  (IntArray.full u_pre n (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((replace_Znth (i_pre) ((Znth j_pre l_u 0)) (l_u)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((replace_Znth (i_pre) ((Znth j_pre l_v 0)) (l_v)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((replace_Znth (i_pre) ((Znth j_pre l_w 0)) (l_w)))) )
).

Definition swap_edge_return_wit_2_split_goal_spatial := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg w_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_w 0)) ((sublist (i_pre) (n) (l_w)))) )
  **  (IntArray.full w_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((sublist (0) (i_pre) (l_w)))) )
  **  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
|--
  (IntArray.full u_pre n (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((replace_Znth (i_pre) ((Znth j_pre l_u 0)) (l_u)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((replace_Znth (i_pre) ((Znth j_pre l_v 0)) (l_v)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((replace_Znth (i_pre) ((Znth j_pre l_w 0)) (l_w)))) )
.

Definition swap_edge_return_wit_3 := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre = j_pre)) (PreH2 : (0 <= i_pre)) (PreH3 : (i_pre < n)) (PreH4 : (0 <= j_pre)) (PreH5 : (j_pre < n)) (PreH6 : ((Zlength (l_u)) = n)) (PreH7 : ((Zlength (l_v)) = n)) (PreH8 : ((Zlength (l_w)) = n)) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (IntArray.full u_pre n (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((replace_Znth (i_pre) ((Znth j_pre l_u 0)) (l_u)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((replace_Znth (i_pre) ((Znth j_pre l_v 0)) (l_v)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_pre) ((Znth i_pre l_w 0)) ((replace_Znth (i_pre) ((Znth j_pre l_w 0)) (l_w)))) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre = j_pre)) (PreH2 : (0 <= i_pre)) (PreH3 : (i_pre < n)) (PreH4 : (0 <= j_pre)) (PreH5 : (j_pre < n)) (PreH6 : ((Zlength (l_u)) = n)) (PreH7 : ((Zlength (l_v)) = n)) (PreH8 : ((Zlength (l_w)) = n)) ,
  TT && emp 
|--
  “ (l_u = (replace_Znth (j_pre) ((Znth j_pre l_u 0)) ((replace_Znth (j_pre) ((Znth j_pre l_u 0)) (l_u))))) ” 
  &&  “ (l_v = (replace_Znth (j_pre) ((Znth j_pre l_v 0)) ((replace_Znth (j_pre) ((Znth j_pre l_v 0)) (l_v))))) ” 
  &&  “ (l_w = (replace_Znth (j_pre) ((Znth j_pre l_w 0)) ((replace_Znth (j_pre) ((Znth j_pre l_w 0)) (l_w))))) ”
  &&  emp
).

Definition swap_edge_return_wit_3_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre = j_pre)) (PreH2 : (0 <= i_pre)) (PreH3 : (i_pre < n)) (PreH4 : (0 <= j_pre)) (PreH5 : (j_pre < n)) (PreH6 : ((Zlength (l_u)) = n)) (PreH7 : ((Zlength (l_v)) = n)) (PreH8 : ((Zlength (l_w)) = n)) ,
  (l_u = (replace_Znth (j_pre) ((Znth j_pre l_u 0)) ((replace_Znth (j_pre) ((Znth j_pre l_u 0)) (l_u)))))
.

Definition swap_edge_return_wit_3_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre = j_pre)) (PreH2 : (0 <= i_pre)) (PreH3 : (i_pre < n)) (PreH4 : (0 <= j_pre)) (PreH5 : (j_pre < n)) (PreH6 : ((Zlength (l_u)) = n)) (PreH7 : ((Zlength (l_v)) = n)) (PreH8 : ((Zlength (l_w)) = n)) ,
  (l_v = (replace_Znth (j_pre) ((Znth j_pre l_v 0)) ((replace_Znth (j_pre) ((Znth j_pre l_v 0)) (l_v)))))
.

Definition swap_edge_return_wit_3_split_goal_3 := 
forall (j_pre: Z) (i_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (i_pre = j_pre)) (PreH2 : (0 <= i_pre)) (PreH3 : (i_pre < n)) (PreH4 : (0 <= j_pre)) (PreH5 : (j_pre < n)) (PreH6 : ((Zlength (l_u)) = n)) (PreH7 : ((Zlength (l_v)) = n)) (PreH8 : ((Zlength (l_w)) = n)) ,
  (l_w = (replace_Znth (j_pre) ((Znth j_pre l_w 0)) ((replace_Znth (j_pre) ((Znth j_pre l_w 0)) (l_w)))))
.

Definition swap_edge_partial_solve_wit_1_pure := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_u 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_u)) 0)) ” 
  &&  “ ((Znth j_pre l_u 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_u)) 0)) ”
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_u 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_u)) 0)) ” 
  &&  “ ((Znth i_pre l_u 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_u)) 0)) ”
).

Definition swap_edge_partial_solve_wit_1_pure_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_u 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_u)) 0)) ”
.

Definition swap_edge_partial_solve_wit_1_pure_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_u 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_u)) 0)) ”
.

Definition swap_edge_partial_solve_wit_1_aux := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg u_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_u 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_u)) 0)) ” 
  &&  “ ((Znth j_pre l_u 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_u)) 0)) ” 
  &&  “ (0 <= i_pre) ” 
  &&  “ (i_pre < j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (((u_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l_u 0))
  **  (((u_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l_u 0))
  **  (IntArray.missing_i u_pre j_pre j_pre n (sublist (j_pre) (n) (l_u)) )
  **  (IntArray.missing_i u_pre i_pre 0 j_pre (sublist (0) (j_pre) (l_u)) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
.

Definition swap_edge_partial_solve_wit_1 := swap_edge_partial_solve_wit_1_pure -> swap_edge_partial_solve_wit_1_aux.

Definition swap_edge_partial_solve_wit_2_pure := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_v 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_v)) 0)) ” 
  &&  “ ((Znth j_pre l_v 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_v)) 0)) ”
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_v 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_v)) 0)) ” 
  &&  “ ((Znth i_pre l_v 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_v)) 0)) ”
).

Definition swap_edge_partial_solve_wit_2_pure_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_v 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_v)) 0)) ”
.

Definition swap_edge_partial_solve_wit_2_pure_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_v 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_v)) 0)) ”
.

Definition swap_edge_partial_solve_wit_2_aux := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  (IntArray.seg v_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg v_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_v 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_v)) 0)) ” 
  &&  “ ((Znth j_pre l_v 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_v)) 0)) ” 
  &&  “ (0 <= i_pre) ” 
  &&  “ (i_pre < j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (((v_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l_v 0))
  **  (((v_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l_v 0))
  **  (IntArray.missing_i v_pre j_pre j_pre n (sublist (j_pre) (n) (l_v)) )
  **  (IntArray.missing_i v_pre i_pre 0 j_pre (sublist (0) (j_pre) (l_v)) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
.

Definition swap_edge_partial_solve_wit_2 := swap_edge_partial_solve_wit_2_pure -> swap_edge_partial_solve_wit_2_aux.

Definition swap_edge_partial_solve_wit_3_pure := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_w 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_w)) 0)) ” 
  &&  “ ((Znth j_pre l_w 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_w)) 0)) ”
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_w 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_w)) 0)) ” 
  &&  “ ((Znth i_pre l_w 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_w)) 0)) ”
).

Definition swap_edge_partial_solve_wit_3_pure_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_w 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_w)) 0)) ”
.

Definition swap_edge_partial_solve_wit_3_pure_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < j_pre)) (PreH7 : (j_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_w 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_w)) 0)) ”
.

Definition swap_edge_partial_solve_wit_3_aux := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < j_pre)) (PreH3 : (j_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
  **  (IntArray.seg w_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg w_pre j_pre n (sublist (j_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_w 0) = (Znth (i_pre - 0 ) (sublist (0) (j_pre) (l_w)) 0)) ” 
  &&  “ ((Znth j_pre l_w 0) = (Znth (j_pre - j_pre ) (sublist (j_pre) (n) (l_w)) 0)) ” 
  &&  “ (0 <= i_pre) ” 
  &&  “ (i_pre < j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (((w_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l_w 0))
  **  (((w_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l_w 0))
  **  (IntArray.missing_i w_pre j_pre j_pre n (sublist (j_pre) (n) (l_w)) )
  **  (IntArray.missing_i w_pre i_pre 0 j_pre (sublist (0) (j_pre) (l_w)) )
  **  (IntArray.seg v_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_v 0)) ((sublist (j_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_v 0)) ((sublist (0) (j_pre) (l_v)))) )
  **  (IntArray.seg u_pre j_pre n (replace_Znth ((j_pre - j_pre )) ((Znth i_pre l_u 0)) ((sublist (j_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre j_pre (replace_Znth (i_pre) ((Znth j_pre l_u 0)) ((sublist (0) (j_pre) (l_u)))) )
.

Definition swap_edge_partial_solve_wit_3 := swap_edge_partial_solve_wit_3_pure -> swap_edge_partial_solve_wit_3_aux.

Definition swap_edge_partial_solve_wit_4_pure := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_u 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_u)) 0)) ” 
  &&  “ ((Znth i_pre l_u 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_u)) 0)) ”
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_u 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_u)) 0)) ” 
  &&  “ ((Znth j_pre l_u 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_u)) 0)) ”
).

Definition swap_edge_partial_solve_wit_4_pure_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_u 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_u)) 0)) ”
.

Definition swap_edge_partial_solve_wit_4_pure_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_u 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_u)) 0)) ”
.

Definition swap_edge_partial_solve_wit_4_aux := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg u_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_u 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_u)) 0)) ” 
  &&  “ ((Znth i_pre l_u 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_u)) 0)) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (((u_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l_u 0))
  **  (((u_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l_u 0))
  **  (IntArray.missing_i u_pre i_pre i_pre n (sublist (i_pre) (n) (l_u)) )
  **  (IntArray.missing_i u_pre j_pre 0 i_pre (sublist (0) (i_pre) (l_u)) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
.

Definition swap_edge_partial_solve_wit_4 := swap_edge_partial_solve_wit_4_pure -> swap_edge_partial_solve_wit_4_aux.

Definition swap_edge_partial_solve_wit_5_pure := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_v 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_v)) 0)) ” 
  &&  “ ((Znth i_pre l_v 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_v)) 0)) ”
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_v 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_v)) 0)) ” 
  &&  “ ((Znth j_pre l_v 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_v)) 0)) ”
).

Definition swap_edge_partial_solve_wit_5_pure_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_v 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_v)) 0)) ”
.

Definition swap_edge_partial_solve_wit_5_pure_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_v 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_v)) 0)) ”
.

Definition swap_edge_partial_solve_wit_5_aux := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  (IntArray.seg v_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg v_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_v 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_v)) 0)) ” 
  &&  “ ((Znth i_pre l_v 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_v)) 0)) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (((v_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l_v 0))
  **  (((v_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l_v 0))
  **  (IntArray.missing_i v_pre i_pre i_pre n (sublist (i_pre) (n) (l_v)) )
  **  (IntArray.missing_i v_pre j_pre 0 i_pre (sublist (0) (i_pre) (l_v)) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
.

Definition swap_edge_partial_solve_wit_5 := swap_edge_partial_solve_wit_5_pure -> swap_edge_partial_solve_wit_5_aux.

Definition swap_edge_partial_solve_wit_6_pure := 
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_w 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_w)) 0)) ” 
  &&  “ ((Znth i_pre l_w 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_w)) 0)) ”
) \/
(
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_w 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_w)) 0)) ” 
  &&  “ ((Znth j_pre l_w 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_w)) 0)) ”
).

Definition swap_edge_partial_solve_wit_6_pure_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth i_pre l_w 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_w)) 0)) ”
.

Definition swap_edge_partial_solve_wit_6_pure_split_goal_2 := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (j_pre <= INT_MAX)) (PreH2 : (i_pre <= INT_MAX)) (PreH3 : (j_pre >= INT_MIN)) (PreH4 : (i_pre >= INT_MIN)) (PreH5 : (0 <= j_pre)) (PreH6 : (j_pre < i_pre)) (PreH7 : (i_pre < n)) (PreH8 : ((Zlength (l_u)) = n)) (PreH9 : ((Zlength (l_v)) = n)) (PreH10 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "j" ) )) # Int  |-> j_pre)
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_w 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_w)) 0)) ”
.

Definition swap_edge_partial_solve_wit_6_aux := 
forall (j_pre: Z) (i_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (n: Z) (PreH1 : (0 <= j_pre)) (PreH2 : (j_pre < i_pre)) (PreH3 : (i_pre < n)) (PreH4 : ((Zlength (l_u)) = n)) (PreH5 : ((Zlength (l_v)) = n)) (PreH6 : ((Zlength (l_w)) = n)) ,
  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
  **  (IntArray.seg w_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg w_pre i_pre n (sublist (i_pre) (n) (l_w)) )
|--
  “ ((Znth j_pre l_w 0) = (Znth (j_pre - 0 ) (sublist (0) (i_pre) (l_w)) 0)) ” 
  &&  “ ((Znth i_pre l_w 0) = (Znth (i_pre - i_pre ) (sublist (i_pre) (n) (l_w)) 0)) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ ((Zlength (l_u)) = n) ” 
  &&  “ ((Zlength (l_v)) = n) ” 
  &&  “ ((Zlength (l_w)) = n) ”
  &&  (((w_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l_w 0))
  **  (((w_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l_w 0))
  **  (IntArray.missing_i w_pre i_pre i_pre n (sublist (i_pre) (n) (l_w)) )
  **  (IntArray.missing_i w_pre j_pre 0 i_pre (sublist (0) (i_pre) (l_w)) )
  **  (IntArray.seg v_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_v 0)) ((sublist (i_pre) (n) (l_v)))) )
  **  (IntArray.full v_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_v 0)) ((sublist (0) (i_pre) (l_v)))) )
  **  (IntArray.seg u_pre i_pre n (replace_Znth ((i_pre - i_pre )) ((Znth j_pre l_u 0)) ((sublist (i_pre) (n) (l_u)))) )
  **  (IntArray.full u_pre i_pre (replace_Znth (j_pre) ((Znth i_pre l_u 0)) ((sublist (0) (i_pre) (l_u)))) )
.

Definition swap_edge_partial_solve_wit_6 := swap_edge_partial_solve_wit_6_pure -> swap_edge_partial_solve_wit_6_aux.

(*----- Function partitionByWeight -----*)

Definition partitionByWeight_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : ((Zlength (l_u1)) = n)) (PreH2 : ((Zlength (l_v1)) = n)) (PreH3 : ((Zlength (l_w1)) = n)) (PreH4 : ((Znth j l_w1 0) < pivot_w)) (PreH5 : (j < right_pre)) (PreH6 : (pivot_w = (Znth right_pre l_w 0))) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) (PreH12 : (left_pre <= i)) (PreH13 : (i <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH16 : (Permutation edge_order edge_order1 )) (PreH17 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH18 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH19 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH20 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full u_pre n (replace_Znth (j) ((Znth i l_u1 0)) ((replace_Znth (i) ((Znth j l_u1 0)) (l_u1)))) )
  **  (IntArray.full v_pre n (replace_Znth (j) ((Znth i l_v1 0)) ((replace_Znth (i) ((Znth j l_v1 0)) (l_v1)))) )
  **  (IntArray.full w_pre n (replace_Znth (j) ((Znth i l_w1 0)) ((replace_Znth (i) ((Znth j l_w1 0)) (l_w1)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partitionByWeight_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : ((Zlength (l_u1)) = n)) (PreH2 : ((Zlength (l_v1)) = n)) (PreH3 : ((Zlength (l_w1)) = n)) (PreH4 : ((Znth j l_w1 0) < pivot_w)) (PreH5 : (j < right_pre)) (PreH6 : (pivot_w = (Znth right_pre l_w 0))) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) (PreH12 : (left_pre <= i)) (PreH13 : (i <= j)) (PreH14 : (j <= right_pre)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH16 : (Permutation edge_order edge_order1 )) (PreH17 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH18 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH19 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH20 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full u_pre n (replace_Znth (j) ((Znth i l_u1 0)) ((replace_Znth (i) ((Znth j l_u1 0)) (l_u1)))) )
  **  (IntArray.full v_pre n (replace_Znth (j) ((Znth i l_v1 0)) ((replace_Znth (i) ((Znth j l_v1 0)) (l_v1)))) )
  **  (IntArray.full w_pre n (replace_Znth (j) ((Znth i l_w1 0)) ((replace_Znth (i) ((Znth j l_w1 0)) (l_w1)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partitionByWeight_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : ((Znth j l_w1 0) >= pivot_w)) (PreH2 : (j < right_pre)) (PreH3 : (pivot_w = (Znth right_pre l_w 0))) (PreH4 : (0 <= n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n)) (PreH9 : (left_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= right_pre)) (PreH12 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH13 : (Permutation edge_order edge_order1 )) (PreH14 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH15 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH16 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH17 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full w_pre n l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partitionByWeight_entail_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre <= right_pre)) (PreH5 : (right_pre < n)) (PreH6 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  ((( &( "j" ) )) # Int  |-> left_pre)
  **  ((( &( "i" ) )) # Int  |-> left_pre)
  **  (IntArray.full w_pre n l_w )
  **  ((( &( "pivot_w" ) )) # Int  |-> (Znth right_pre l_w 0))
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z))  (j: Z)  (i: Z)  (pivot_w: Z) ,
  “ (pivot_w = (Znth right_pre l_w 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w)) ” 
  &&  “ forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0))) ” 
  &&  “ ((Znth right_pre l_w1 0) = pivot_w) ”
  &&  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : ((Zlength (l_v)) = n)) (PreH2 : ((Zlength (l_u)) = n)) (PreH3 : ((Zlength (l_w)) = n)) (PreH4 : (0 <= n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n)) (PreH9 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (left_pre <= left_pre) ” 
  &&  “ (left_pre <= left_pre) ” 
  &&  “ (edge_arrays_ordered_by (Zlength (l_v)) orig_u orig_v orig_w l_u l_v l_w edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u l_v l_w edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < left_pre)) -> ((Znth k l_w 0) < (Znth right_pre l_w 0))) ” 
  &&  “ forall (k_2: Z) , (((left_pre <= k_2) /\ (k_2 < left_pre)) -> ((Znth right_pre l_w 0) <= (Znth k_2 l_w 0))) ”
  &&  emp
).

Definition partitionByWeight_entail_wit_2_1 := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_w_2: Z) (PreH1 : ((Zlength (l_u1_2)) = n)) (PreH2 : ((Zlength (l_v1_2)) = n)) (PreH3 : ((Zlength (l_w1_2)) = n)) (PreH4 : ((Znth j_2 l_w1_2 0) < pivot_w_2)) (PreH5 : (j_2 < right_pre)) (PreH6 : (pivot_w_2 = (Znth right_pre l_w 0))) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) (PreH12 : (left_pre <= i_2)) (PreH13 : (i_2 <= j_2)) (PreH14 : (j_2 <= right_pre)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH16 : (Permutation edge_order edge_order1_2 )) (PreH17 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH18 : forall (k: Z) , (((left_pre <= k) /\ (k < i_2)) -> ((Znth k l_w1_2 0) < pivot_w_2))) (PreH19 : forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < j_2)) -> (pivot_w_2 <= (Znth k_2 l_w1_2 0)))) (PreH20 : ((Znth right_pre l_w1_2 0) = pivot_w_2)) ,
  (IntArray.full u_pre n (replace_Znth (j_2) ((Znth i_2 l_u1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_u1_2 0)) (l_u1_2)))) )
  **  (IntArray.full v_pre n (replace_Znth (j_2) ((Znth i_2 l_v1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_v1_2 0)) (l_v1_2)))) )
  **  (IntArray.full w_pre n (replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))) )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w_2)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z))  (j: Z)  (i: Z)  (pivot_w: Z) ,
  “ (pivot_w = (Znth right_pre l_w 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w)) ” 
  &&  “ forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0))) ” 
  &&  “ ((Znth right_pre l_w1 0) = pivot_w) ”
  &&  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_w_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))))) = n)) (PreH2 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l_v1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_v1_2 0)) (l_v1_2)))))) = n)) (PreH3 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l_u1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_u1_2 0)) (l_u1_2)))))) = n)) (PreH4 : ((Zlength (l_u1_2)) = n)) (PreH5 : ((Zlength (l_v1_2)) = n)) (PreH6 : ((Zlength (l_w1_2)) = n)) (PreH7 : ((Znth j_2 l_w1_2 0) < pivot_w_2)) (PreH8 : (j_2 < right_pre)) (PreH9 : (pivot_w_2 = (Znth right_pre l_w 0))) (PreH10 : (0 <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : (0 <= left_pre)) (PreH13 : (left_pre <= right_pre)) (PreH14 : (right_pre < n)) (PreH15 : (left_pre <= i_2)) (PreH16 : (i_2 <= j_2)) (PreH17 : (j_2 <= right_pre)) (PreH18 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH19 : (Permutation edge_order edge_order1_2 )) (PreH20 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH21 : forall (k: Z) , (((left_pre <= k) /\ (k < i_2)) -> ((Znth k l_w1_2 0) < pivot_w_2))) (PreH22 : forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < j_2)) -> (pivot_w_2 <= (Znth k_2 l_w1_2 0)))) (PreH23 : ((Znth right_pre l_w1_2 0) = pivot_w_2)) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (left_pre <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= (j_2 + 1 )) ” 
  &&  “ ((j_2 + 1 ) <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by (Zlength ((replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))))) orig_u orig_v orig_w (replace_Znth (j_2) ((Znth i_2 l_u1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_u1_2 0)) (l_u1_2)))) (replace_Znth (j_2) ((Znth i_2 l_v1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_v1_2 0)) (l_v1_2)))) (replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))) edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order (replace_Znth (j_2) ((Znth i_2 l_u1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_u1_2 0)) (l_u1_2)))) (replace_Znth (j_2) ((Znth i_2 l_v1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_v1_2 0)) (l_v1_2)))) (replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))) edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < (i_2 + 1 ))) -> ((Znth k (replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))) 0) < (Znth right_pre l_w 0))) ” 
  &&  “ forall (k_2: Z) , ((((i_2 + 1 ) <= k_2) /\ (k_2 < (j_2 + 1 ))) -> ((Znth right_pre l_w 0) <= (Znth k_2 (replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))) 0))) ” 
  &&  “ ((Znth right_pre (replace_Znth (j_2) ((Znth i_2 l_w1_2 0)) ((replace_Znth (i_2) ((Znth j_2 l_w1_2 0)) (l_w1_2)))) 0) = (Znth right_pre l_w 0)) ”
  &&  emp
).

Definition partitionByWeight_entail_wit_2_2 := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_w_2: Z) (PreH1 : ((Znth j_2 l_w1_2 0) >= pivot_w_2)) (PreH2 : (j_2 < right_pre)) (PreH3 : (pivot_w_2 = (Znth right_pre l_w 0))) (PreH4 : (0 <= n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n)) (PreH9 : (left_pre <= i_2)) (PreH10 : (i_2 <= j_2)) (PreH11 : (j_2 <= right_pre)) (PreH12 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH13 : (Permutation edge_order edge_order1_2 )) (PreH14 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH15 : forall (k: Z) , (((left_pre <= k) /\ (k < i_2)) -> ((Znth k l_w1_2 0) < pivot_w_2))) (PreH16 : forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < j_2)) -> (pivot_w_2 <= (Znth k_2 l_w1_2 0)))) (PreH17 : ((Znth right_pre l_w1_2 0) = pivot_w_2)) ,
  (IntArray.full w_pre n l_w1_2 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
  **  (IntArray.full u_pre n l_u1_2 )
  **  (IntArray.full v_pre n l_v1_2 )
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z))  (j: Z)  (i: Z)  (pivot_w: Z) ,
  “ (pivot_w = (Znth right_pre l_w 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w)) ” 
  &&  “ forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0))) ” 
  &&  “ ((Znth right_pre l_w1 0) = pivot_w) ”
  &&  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_w_2: Z) (PreH1 : ((Zlength (l_v1_2)) = n)) (PreH2 : ((Zlength (l_u1_2)) = n)) (PreH3 : ((Zlength (l_w1_2)) = n)) (PreH4 : ((Znth j_2 l_w1_2 0) >= pivot_w_2)) (PreH5 : (j_2 < right_pre)) (PreH6 : (pivot_w_2 = (Znth right_pre l_w 0))) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) (PreH12 : (left_pre <= i_2)) (PreH13 : (i_2 <= j_2)) (PreH14 : (j_2 <= right_pre)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH16 : (Permutation edge_order edge_order1_2 )) (PreH17 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH18 : forall (k: Z) , (((left_pre <= k) /\ (k < i_2)) -> ((Znth k l_w1_2 0) < pivot_w_2))) (PreH19 : forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < j_2)) -> (pivot_w_2 <= (Znth k_2 l_w1_2 0)))) (PreH20 : ((Znth right_pre l_w1_2 0) = pivot_w_2)) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (i_2 <= (j_2 + 1 )) ” 
  &&  “ ((j_2 + 1 ) <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by (Zlength (l_v1_2)) orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < i_2)) -> ((Znth k l_w1_2 0) < (Znth right_pre l_w 0))) ” 
  &&  “ forall (k_2: Z) , (((i_2 <= k_2) /\ (k_2 < (j_2 + 1 ))) -> ((Znth right_pre l_w 0) <= (Znth k_2 l_w1_2 0))) ” 
  &&  “ ((Znth right_pre l_w1_2 0) = (Znth right_pre l_w 0)) ”
  &&  emp
).

Definition partitionByWeight_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : ((Zlength (l_u1_2)) = n)) (PreH2 : ((Zlength (l_v1_2)) = n)) (PreH3 : ((Zlength (l_w1_2)) = n)) (PreH4 : (j >= right_pre)) (PreH5 : (pivot_w = (Znth right_pre l_w 0))) (PreH6 : (0 <= n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH15 : (Permutation edge_order edge_order1_2 )) (PreH16 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH17 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1_2 0) < pivot_w))) (PreH18 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1_2 0)))) (PreH19 : ((Znth right_pre l_w1_2 0) = pivot_w)) ,
  (IntArray.full u_pre n (replace_Znth (right_pre) ((Znth i l_u1_2 0)) ((replace_Znth (i) ((Znth right_pre l_u1_2 0)) (l_u1_2)))) )
  **  (IntArray.full v_pre n (replace_Znth (right_pre) ((Znth i l_v1_2 0)) ((replace_Znth (i) ((Znth right_pre l_v1_2 0)) (l_v1_2)))) )
  **  (IntArray.full w_pre n (replace_Znth (right_pre) ((Znth i l_w1_2 0)) ((replace_Znth (i) ((Znth right_pre l_w1_2 0)) (l_w1_2)))) )
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre i ) ”
  &&  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : ((Zlength (l_u1_2)) = n)) (PreH2 : ((Zlength (l_v1_2)) = n)) (PreH3 : ((Zlength (l_w1_2)) = n)) (PreH4 : (j >= right_pre)) (PreH5 : (pivot_w = (Znth right_pre l_w 0))) (PreH6 : (0 <= n)) (PreH7 : (n <= INT_MAX)) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n)) (PreH11 : (left_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= right_pre)) (PreH14 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH15 : (Permutation edge_order edge_order1_2 )) (PreH16 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH17 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1_2 0) < pivot_w))) (PreH18 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1_2 0)))) (PreH19 : ((Znth right_pre l_w1_2 0) = pivot_w)) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (i <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by (Zlength (l_u1_2)) orig_u orig_v orig_w (replace_Znth (right_pre) ((Znth i l_u1_2 0)) ((replace_Znth (i) ((Znth right_pre l_u1_2 0)) (l_u1_2)))) (replace_Znth (right_pre) ((Znth i l_v1_2 0)) ((replace_Znth (i) ((Znth right_pre l_v1_2 0)) (l_v1_2)))) (replace_Znth (right_pre) ((Znth i l_w1_2 0)) ((replace_Znth (i) ((Znth right_pre l_w1_2 0)) (l_w1_2)))) edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order (replace_Znth (right_pre) ((Znth i l_u1_2 0)) ((replace_Znth (i) ((Znth right_pre l_u1_2 0)) (l_u1_2)))) (replace_Znth (right_pre) ((Znth i l_v1_2 0)) ((replace_Znth (i) ((Znth right_pre l_v1_2 0)) (l_v1_2)))) (replace_Znth (right_pre) ((Znth i l_w1_2 0)) ((replace_Znth (i) ((Znth right_pre l_w1_2 0)) (l_w1_2)))) edge_order1 left_pre right_pre ) ” 
  &&  “ (edge_arrays_partitioned_by_weight_at (replace_Znth (right_pre) ((Znth i l_w1_2 0)) ((replace_Znth (i) ((Znth right_pre l_w1_2 0)) (l_w1_2)))) left_pre right_pre i ) ”
  &&  emp
).

Definition partitionByWeight_partial_solve_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre <= right_pre)) (PreH5 : (right_pre < n)) (PreH6 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order ) ”
  &&  (((w_pre + (right_pre * sizeof(INT)))) # Int  |-> (Znth right_pre l_w 0))
  **  (IntArray.missing_i w_pre right_pre 0 n l_w )
  **  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
.

Definition partitionByWeight_partial_solve_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (j < right_pre)) (PreH2 : (pivot_w = (Znth right_pre l_w 0))) (PreH3 : (0 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre < n)) (PreH8 : (left_pre <= i)) (PreH9 : (i <= j)) (PreH10 : (j <= right_pre)) (PreH11 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH12 : (Permutation edge_order edge_order1 )) (PreH13 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH14 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH15 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH16 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ (j < right_pre) ” 
  &&  “ (pivot_w = (Znth right_pre l_w 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w)) ” 
  &&  “ forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0))) ” 
  &&  “ ((Znth right_pre l_w1 0) = pivot_w) ”
  &&  (((w_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l_w1 0))
  **  (IntArray.missing_i w_pre j 0 n l_w1 )
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
.

Definition partitionByWeight_partial_solve_wit_3_pure := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : ((Znth j l_w1 0) < pivot_w)) (PreH2 : (j < right_pre)) (PreH3 : (pivot_w = (Znth right_pre l_w 0))) (PreH4 : (0 <= n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n)) (PreH9 : (left_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= right_pre)) (PreH12 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH13 : (Permutation edge_order edge_order1 )) (PreH14 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH15 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH16 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH17 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full w_pre n l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ ((Zlength (l_w1)) = n) ” 
  &&  “ ((Zlength (l_v1)) = n) ” 
  &&  “ ((Zlength (l_u1)) = n) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (pivot_w <= INT_MAX)) (PreH4 : (right_pre <= INT_MAX)) (PreH5 : (left_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (pivot_w >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : ((Znth j l_w1 0) < pivot_w)) (PreH12 : (j < right_pre)) (PreH13 : (pivot_w = (Znth right_pre l_w 0))) (PreH14 : (0 <= n)) (PreH15 : (n <= INT_MAX)) (PreH16 : (0 <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre < n)) (PreH19 : (left_pre <= i)) (PreH20 : (i <= j)) (PreH21 : (j <= right_pre)) (PreH22 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH23 : (Permutation edge_order edge_order1 )) (PreH24 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH25 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH26 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH27 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full w_pre n l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
|--
  “ ((Zlength (l_u1)) = n) ” 
  &&  “ ((Zlength (l_v1)) = n) ” 
  &&  “ ((Zlength (l_w1)) = n) ”
).

Definition partitionByWeight_partial_solve_wit_3_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (pivot_w <= INT_MAX)) (PreH4 : (right_pre <= INT_MAX)) (PreH5 : (left_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (pivot_w >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : ((Znth j l_w1 0) < pivot_w)) (PreH12 : (j < right_pre)) (PreH13 : (pivot_w = (Znth right_pre l_w 0))) (PreH14 : (0 <= n)) (PreH15 : (n <= INT_MAX)) (PreH16 : (0 <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre < n)) (PreH19 : (left_pre <= i)) (PreH20 : (i <= j)) (PreH21 : (j <= right_pre)) (PreH22 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH23 : (Permutation edge_order edge_order1 )) (PreH24 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH25 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH26 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH27 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full w_pre n l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
|--
  “ ((Zlength (l_u1)) = n) ”
.

Definition partitionByWeight_partial_solve_wit_3_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (pivot_w <= INT_MAX)) (PreH4 : (right_pre <= INT_MAX)) (PreH5 : (left_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (pivot_w >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : ((Znth j l_w1 0) < pivot_w)) (PreH12 : (j < right_pre)) (PreH13 : (pivot_w = (Znth right_pre l_w 0))) (PreH14 : (0 <= n)) (PreH15 : (n <= INT_MAX)) (PreH16 : (0 <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre < n)) (PreH19 : (left_pre <= i)) (PreH20 : (i <= j)) (PreH21 : (j <= right_pre)) (PreH22 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH23 : (Permutation edge_order edge_order1 )) (PreH24 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH25 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH26 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH27 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full w_pre n l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
|--
  “ ((Zlength (l_v1)) = n) ”
.

Definition partitionByWeight_partial_solve_wit_3_pure_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (pivot_w <= INT_MAX)) (PreH4 : (right_pre <= INT_MAX)) (PreH5 : (left_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (pivot_w >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : ((Znth j l_w1 0) < pivot_w)) (PreH12 : (j < right_pre)) (PreH13 : (pivot_w = (Znth right_pre l_w 0))) (PreH14 : (0 <= n)) (PreH15 : (n <= INT_MAX)) (PreH16 : (0 <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre < n)) (PreH19 : (left_pre <= i)) (PreH20 : (i <= j)) (PreH21 : (j <= right_pre)) (PreH22 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH23 : (Permutation edge_order edge_order1 )) (PreH24 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH25 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH26 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH27 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full w_pre n l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
|--
  “ ((Zlength (l_w1)) = n) ”
.

Definition partitionByWeight_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : ((Znth j l_w1 0) < pivot_w)) (PreH2 : (j < right_pre)) (PreH3 : (pivot_w = (Znth right_pre l_w 0))) (PreH4 : (0 <= n)) (PreH5 : (n <= INT_MAX)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre <= right_pre)) (PreH8 : (right_pre < n)) (PreH9 : (left_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= right_pre)) (PreH12 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH13 : (Permutation edge_order edge_order1 )) (PreH14 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH15 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH16 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH17 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full w_pre n l_w1 )
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ ((Zlength (l_w1)) = n) ” 
  &&  “ ((Zlength (l_v1)) = n) ” 
  &&  “ ((Zlength (l_u1)) = n) ” 
  &&  “ ((Znth j l_w1 0) < pivot_w) ” 
  &&  “ (j < right_pre) ” 
  &&  “ (pivot_w = (Znth right_pre l_w 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w)) ” 
  &&  “ forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0))) ” 
  &&  “ ((Znth right_pre l_w1 0) = pivot_w) ”
  &&  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
.

Definition partitionByWeight_partial_solve_wit_3 := partitionByWeight_partial_solve_wit_3_pure -> partitionByWeight_partial_solve_wit_3_aux.

Definition partitionByWeight_partial_solve_wit_4_pure := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (j >= right_pre)) (PreH2 : (pivot_w = (Znth right_pre l_w 0))) (PreH3 : (0 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre < n)) (PreH8 : (left_pre <= i)) (PreH9 : (i <= j)) (PreH10 : (j <= right_pre)) (PreH11 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH12 : (Permutation edge_order edge_order1 )) (PreH13 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH14 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH15 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH16 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ ((Zlength (l_w1)) = n) ” 
  &&  “ ((Zlength (l_v1)) = n) ” 
  &&  “ ((Zlength (l_u1)) = n) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (pivot_w <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (pivot_w >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (j >= right_pre)) (PreH10 : (pivot_w = (Znth right_pre l_w 0))) (PreH11 : (0 <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) (PreH16 : (left_pre <= i)) (PreH17 : (i <= j)) (PreH18 : (j <= right_pre)) (PreH19 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH20 : (Permutation edge_order edge_order1 )) (PreH21 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH22 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH23 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH24 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ ((Zlength (l_u1)) = n) ” 
  &&  “ ((Zlength (l_v1)) = n) ” 
  &&  “ ((Zlength (l_w1)) = n) ”
).

Definition partitionByWeight_partial_solve_wit_4_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (pivot_w <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (pivot_w >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (j >= right_pre)) (PreH10 : (pivot_w = (Znth right_pre l_w 0))) (PreH11 : (0 <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) (PreH16 : (left_pre <= i)) (PreH17 : (i <= j)) (PreH18 : (j <= right_pre)) (PreH19 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH20 : (Permutation edge_order edge_order1 )) (PreH21 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH22 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH23 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH24 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ ((Zlength (l_u1)) = n) ”
.

Definition partitionByWeight_partial_solve_wit_4_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (pivot_w <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (pivot_w >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (j >= right_pre)) (PreH10 : (pivot_w = (Znth right_pre l_w 0))) (PreH11 : (0 <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) (PreH16 : (left_pre <= i)) (PreH17 : (i <= j)) (PreH18 : (j <= right_pre)) (PreH19 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH20 : (Permutation edge_order edge_order1 )) (PreH21 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH22 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH23 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH24 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ ((Zlength (l_v1)) = n) ”
.

Definition partitionByWeight_partial_solve_wit_4_pure_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (pivot_w <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (pivot_w >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (j >= right_pre)) (PreH10 : (pivot_w = (Znth right_pre l_w 0))) (PreH11 : (0 <= n)) (PreH12 : (n <= INT_MAX)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) (PreH16 : (left_pre <= i)) (PreH17 : (i <= j)) (PreH18 : (j <= right_pre)) (PreH19 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH20 : (Permutation edge_order edge_order1 )) (PreH21 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH22 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH23 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH24 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot_w" ) )) # Int  |-> pivot_w)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ ((Zlength (l_w1)) = n) ”
.

Definition partitionByWeight_partial_solve_wit_4_aux := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (j: Z) (i: Z) (pivot_w: Z) (PreH1 : (j >= right_pre)) (PreH2 : (pivot_w = (Znth right_pre l_w 0))) (PreH3 : (0 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre < n)) (PreH8 : (left_pre <= i)) (PreH9 : (i <= j)) (PreH10 : (j <= right_pre)) (PreH11 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH12 : (Permutation edge_order edge_order1 )) (PreH13 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH14 : forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w))) (PreH15 : forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0)))) (PreH16 : ((Znth right_pre l_w1 0) = pivot_w)) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ ((Zlength (l_w1)) = n) ” 
  &&  “ ((Zlength (l_v1)) = n) ” 
  &&  “ ((Zlength (l_u1)) = n) ” 
  &&  “ (j >= right_pre) ” 
  &&  “ (pivot_w = (Znth right_pre l_w 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (left_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ forall (k: Z) , (((left_pre <= k) /\ (k < i)) -> ((Znth k l_w1 0) < pivot_w)) ” 
  &&  “ forall (k_2: Z) , (((i <= k_2) /\ (k_2 < j)) -> (pivot_w <= (Znth k_2 l_w1 0))) ” 
  &&  “ ((Znth right_pre l_w1 0) = pivot_w) ”
  &&  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
.

Definition partitionByWeight_partial_solve_wit_4 := partitionByWeight_partial_solve_wit_4_pure -> partitionByWeight_partial_solve_wit_4_aux.

(*----- Function quickByWeightRange -----*)

Definition quickByWeightRange_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation edge_order edge_order1 )) (PreH7 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH8 : (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quickByWeightRange_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation edge_order edge_order1 )) (PreH7 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH8 : (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quickByWeightRange_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (retval: Z) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH4 : (Permutation edge_order1 edge_order1_2 )) (PreH5 : (same_outside_edge_arrays_range l_u1 l_v1 l_w1 edge_order1 l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre (retval - 1 ) )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1_2 left_pre (retval - 1 ) )) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH12 : (Permutation edge_order edge_order1 )) (PreH13 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH14 : (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n)) (PreH17 : (n <= INT_MAX)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n)) (PreH21 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1_2 )
  **  (IntArray.full v_pre n l_v1_2 )
  **  (IntArray.full w_pre n l_w1_2 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quickByWeightRange_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (retval: Z) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH4 : (Permutation edge_order1 edge_order1_2 )) (PreH5 : (same_outside_edge_arrays_range l_u1 l_v1 l_w1 edge_order1 l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre (retval - 1 ) )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1_2 left_pre (retval - 1 ) )) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH12 : (Permutation edge_order edge_order1 )) (PreH13 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH14 : (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n)) (PreH17 : (n <= INT_MAX)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n)) (PreH21 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1_2 )
  **  (IntArray.full v_pre n l_v1_2 )
  **  (IntArray.full w_pre n l_w1_2 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quickByWeightRange_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (retval: Z) (l_u1_3: (@list Z)) (l_v1_3: (@list Z)) (l_w1_3: (@list Z)) (edge_order1_3: (@list Z)) (l_u1_4: (@list Z)) (l_v1_4: (@list Z)) (l_w1_4: (@list Z)) (edge_order1_4: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_4 l_v1_4 l_w1_4 edge_order1_4 )) (PreH4 : (Permutation edge_order1_3 edge_order1_4 )) (PreH5 : (same_outside_edge_arrays_range l_u1_3 l_v1_3 l_w1_3 edge_order1_3 l_u1_4 l_v1_4 l_w1_4 edge_order1_4 (retval + 1 ) right_pre )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1_4 (retval + 1 ) right_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_3 l_v1_3 l_w1_3 edge_order1_3 )) (PreH10 : (Permutation edge_order1_2 edge_order1_3 )) (PreH11 : (same_outside_edge_arrays_range l_u1_2 l_v1_2 l_w1_2 edge_order1_2 l_u1_3 l_v1_3 l_w1_3 edge_order1_3 left_pre (retval - 1 ) )) (PreH12 : (edge_arrays_range_sorted_by_weight l_w1_3 left_pre (retval - 1 ) )) (PreH13 : (0 <= n)) (PreH14 : (n <= INT_MAX)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH18 : (Permutation edge_order edge_order1_2 )) (PreH19 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH20 : (edge_arrays_partitioned_by_weight_at l_w1_2 left_pre right_pre retval )) (PreH21 : (left_pre < right_pre)) (PreH22 : (0 <= n)) (PreH23 : (n <= INT_MAX)) (PreH24 : (0 <= left_pre)) (PreH25 : ((-1) <= right_pre)) (PreH26 : (right_pre < n)) (PreH27 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1_4 )
  **  (IntArray.full v_pre n l_v1_4 )
  **  (IntArray.full w_pre n l_w1_4 )
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ (edge_arrays_range_sorted_by_weight l_w1 left_pre right_pre ) ”
  &&  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (retval: Z) (l_u1_3: (@list Z)) (l_v1_3: (@list Z)) (l_w1_3: (@list Z)) (edge_order1_3: (@list Z)) (l_u1_4: (@list Z)) (l_v1_4: (@list Z)) (l_w1_4: (@list Z)) (edge_order1_4: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_4 l_v1_4 l_w1_4 edge_order1_4 )) (PreH4 : (Permutation edge_order1_3 edge_order1_4 )) (PreH5 : (same_outside_edge_arrays_range l_u1_3 l_v1_3 l_w1_3 edge_order1_3 l_u1_4 l_v1_4 l_w1_4 edge_order1_4 (retval + 1 ) right_pre )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1_4 (retval + 1 ) right_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_3 l_v1_3 l_w1_3 edge_order1_3 )) (PreH10 : (Permutation edge_order1_2 edge_order1_3 )) (PreH11 : (same_outside_edge_arrays_range l_u1_2 l_v1_2 l_w1_2 edge_order1_2 l_u1_3 l_v1_3 l_w1_3 edge_order1_3 left_pre (retval - 1 ) )) (PreH12 : (edge_arrays_range_sorted_by_weight l_w1_3 left_pre (retval - 1 ) )) (PreH13 : (0 <= n)) (PreH14 : (n <= INT_MAX)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH18 : (Permutation edge_order edge_order1_2 )) (PreH19 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH20 : (edge_arrays_partitioned_by_weight_at l_w1_2 left_pre right_pre retval )) (PreH21 : (left_pre < right_pre)) (PreH22 : (0 <= n)) (PreH23 : (n <= INT_MAX)) (PreH24 : (0 <= left_pre)) (PreH25 : ((-1) <= right_pre)) (PreH26 : (right_pre < n)) (PreH27 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_4 l_v1_4 l_w1_4 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_4 l_v1_4 l_w1_4 edge_order1 left_pre right_pre ) ” 
  &&  “ (edge_arrays_range_sorted_by_weight l_w1_4 left_pre right_pre ) ”
  &&  emp
).

Definition quickByWeightRange_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n)) (PreH7 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ (edge_arrays_range_sorted_by_weight l_w1 left_pre right_pre ) ”
  &&  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n)) (PreH7 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u l_v l_w edge_order1 left_pre right_pre ) ” 
  &&  “ (edge_arrays_range_sorted_by_weight l_w left_pre right_pre ) ”
  &&  emp
).

Definition quickByWeightRange_partial_solve_wit_1_pure := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n)) (PreH7 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  ((( &( "pivot" ) )) # Int  |->_)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order ) ”
.

Definition quickByWeightRange_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n)) (PreH7 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order ) ”
  &&  (IntArray.full u_pre n l_u )
  **  (IntArray.full v_pre n l_v )
  **  (IntArray.full w_pre n l_w )
.

Definition quickByWeightRange_partial_solve_wit_1 := quickByWeightRange_partial_solve_wit_1_pure -> quickByWeightRange_partial_solve_wit_1_aux.

Definition quickByWeightRange_partial_solve_wit_2_pure := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation edge_order edge_order1 )) (PreH7 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH8 : (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ”
.

Definition quickByWeightRange_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation edge_order edge_order1 )) (PreH7 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre )) (PreH8 : (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n)) (PreH11 : (n <= INT_MAX)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n)) (PreH15 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1 l_v1 l_w1 edge_order1 left_pre right_pre ) ” 
  &&  “ (edge_arrays_partitioned_by_weight_at l_w1 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order ) ”
  &&  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
.

Definition quickByWeightRange_partial_solve_wit_2 := quickByWeightRange_partial_solve_wit_2_pure -> quickByWeightRange_partial_solve_wit_2_aux.

Definition quickByWeightRange_partial_solve_wit_3_pure := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (retval: Z) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH4 : (Permutation edge_order1_2 edge_order1 )) (PreH5 : (same_outside_edge_arrays_range l_u1_2 l_v1_2 l_w1_2 edge_order1_2 l_u1 l_v1 l_w1 edge_order1 left_pre (retval - 1 ) )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1 left_pre (retval - 1 ) )) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH12 : (Permutation edge_order edge_order1_2 )) (PreH13 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH14 : (edge_arrays_partitioned_by_weight_at l_w1_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n)) (PreH17 : (n <= INT_MAX)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n)) (PreH21 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ”
.

Definition quickByWeightRange_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (n: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (retval: Z) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 )) (PreH4 : (Permutation edge_order1_2 edge_order1 )) (PreH5 : (same_outside_edge_arrays_range l_u1_2 l_v1_2 l_w1_2 edge_order1_2 l_u1 l_v1 l_w1 edge_order1 left_pre (retval - 1 ) )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1 left_pre (retval - 1 ) )) (PreH7 : (0 <= n)) (PreH8 : (n <= INT_MAX)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH12 : (Permutation edge_order edge_order1_2 )) (PreH13 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre )) (PreH14 : (edge_arrays_partitioned_by_weight_at l_w1_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n)) (PreH17 : (n <= INT_MAX)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n)) (PreH21 : (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order1_2 edge_order1 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u1_2 l_v1_2 l_w1_2 edge_order1_2 l_u1 l_v1 l_w1 edge_order1 left_pre (retval - 1 ) ) ” 
  &&  “ (edge_arrays_range_sorted_by_weight l_w1 left_pre (retval - 1 ) ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 ) ” 
  &&  “ (Permutation edge_order edge_order1_2 ) ” 
  &&  “ (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 left_pre right_pre ) ” 
  &&  “ (edge_arrays_partitioned_by_weight_at l_w1_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (edge_arrays_ordered_by n orig_u orig_v orig_w l_u l_v l_w edge_order ) ”
  &&  (IntArray.full u_pre n l_u1 )
  **  (IntArray.full v_pre n l_v1 )
  **  (IntArray.full w_pre n l_w1 )
.

Definition quickByWeightRange_partial_solve_wit_3 := quickByWeightRange_partial_solve_wit_3_pure -> quickByWeightRange_partial_solve_wit_3_aux.

(*----- Function quickByWeight -----*)

Definition quickByWeight_safety_wit_1 := 
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quickByWeight_safety_wit_2 := 
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition quickByWeight_safety_wit_3 := 
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quickByWeight_safety_wit_4 := 
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quickByWeight_return_wit_1 := 
(
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH4 : (Permutation edge_order edge_order1_2 )) (PreH5 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 0 (n_pre - 1 ) )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1_2 0 (n_pre - 1 ) )) (PreH7 : (n_pre > 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n_pre l_u1_2 )
  **  (IntArray.full v_pre n_pre l_v1_2 )
  **  (IntArray.full w_pre n_pre l_w1_2 )
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (after_sorted_edge_of_input n_pre orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ”
  &&  (IntArray.full u_pre n_pre l_u1 )
  **  (IntArray.full v_pre n_pre l_v1 )
  **  (IntArray.full w_pre n_pre l_w1 )
) \/
(
forall (n_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (l_u1_2: (@list Z)) (l_v1_2: (@list Z)) (l_w1_2: (@list Z)) (edge_order1_2: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1_2 )) (PreH4 : (Permutation edge_order edge_order1_2 )) (PreH5 : (same_outside_edge_arrays_range l_u l_v l_w edge_order l_u1_2 l_v1_2 l_w1_2 edge_order1_2 0 (n_pre - 1 ) )) (PreH6 : (edge_arrays_range_sorted_by_weight l_w1_2 0 (n_pre - 1 ) )) (PreH7 : (n_pre > 0)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (after_sorted_edge_of_input n_pre orig_u orig_v orig_w l_u1_2 l_v1_2 l_w1_2 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ”
  &&  emp
).

Definition quickByWeight_return_wit_2 := 
(
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (n_pre <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
|--
  EX (l_u1: (@list Z))  (l_v1: (@list Z))  (l_w1: (@list Z))  (edge_order1: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (after_sorted_edge_of_input n_pre orig_u orig_v orig_w l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ”
  &&  (IntArray.full u_pre n_pre l_u1 )
  **  (IntArray.full v_pre n_pre l_v1 )
  **  (IntArray.full w_pre n_pre l_w1 )
) \/
(
forall (n_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (n_pre <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  TT && emp 
|--
  EX (edge_order1: (@list Z)) ,
  “ (after_sorted_edge_of_input n_pre orig_u orig_v orig_w l_u l_v l_w edge_order1 ) ” 
  &&  “ (Permutation edge_order edge_order1 ) ”
  &&  emp
).

Definition quickByWeight_partial_solve_wit_1_pure := 
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order ) ”
.

Definition quickByWeight_partial_solve_wit_1_aux := 
forall (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (l_w: (@list Z)) (l_v: (@list Z)) (l_u: (@list Z)) (edge_order: (@list Z)) (orig_w: (@list Z)) (orig_v: (@list Z)) (orig_u: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order )) ,
  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order ) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (edge_arrays_ordered_by n_pre orig_u orig_v orig_w l_u l_v l_w edge_order ) ”
  &&  (IntArray.full u_pre n_pre l_u )
  **  (IntArray.full v_pre n_pre l_v )
  **  (IntArray.full w_pre n_pre l_w )
.

Definition quickByWeight_partial_solve_wit_1 := quickByWeight_partial_solve_wit_1_pure -> quickByWeight_partial_solve_wit_1_aux.

(*----- Function kruskal -----*)

Definition kruskal_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_u" ) )) # Ptr  |->_)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition kruskal_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_u" ) )) # Ptr  |->_)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kruskal_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_v" ) )) # Ptr  |->_)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition kruskal_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_v" ) )) # Ptr  |->_)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kruskal_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_w" ) )) # Ptr  |->_)
  **  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition kruskal_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_w" ) )) # Ptr  |->_)
  **  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kruskal_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "chosen" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_4 (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> retval_4)
  **  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kruskal_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "chosen" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_4 (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> retval_4)
  **  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition kruskal_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre < INT_MAX)) (PreH10 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH11 : (KruskalEnv g_low_level_spec )) (PreH12 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH13 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH14 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH15 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH16 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH17 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition kruskal_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre < INT_MAX)) (PreH10 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH11 : (KruskalEnv g_low_level_spec )) (PreH12 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH13 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH14 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH15 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH16 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH17 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition kruskal_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (root_u <> root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u 0))) (PreH8 : (edge_v = (Znth i l_v 0))) (PreH9 : (edge_w = (Znth i l_w 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of (edge_u)))) (PreH19 : (root_v = (repr_of (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH28 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH31 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg out_w 0 (chosen + 1 ) (app (l_out_w) ((cons (edge_w) ((@nil Z))))) )
  **  (IntArray.undef_seg out_w (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 (chosen + 1 ) (app (l_out_v) ((cons (edge_v) ((@nil Z))))) )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "edge_u" ) )) # Int  |-> edge_u)
  **  ((( &( "edge_v" ) )) # Int  |-> edge_v)
  **  ((( &( "edge_w" ) )) # Int  |-> edge_w)
  **  ((( &( "root_u" ) )) # Int  |-> root_u)
  **  ((( &( "root_v" ) )) # Int  |-> root_v)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
|--
  “ ((chosen + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (chosen + 1 )) ”
.

Definition kruskal_safety_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (s_after: St) (repr_of_after: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (0 <= i)) (PreH2 : (i < m_pre)) (PreH3 : (0 <= chosen)) (PreH4 : (chosen <= (n_pre - 1 ))) (PreH5 : (edge_u = (Znth i l_u 0))) (PreH6 : (edge_v = (Znth i l_v 0))) (PreH7 : (edge_w = (Znth i l_w 0))) (PreH8 : (0 <= edge_u)) (PreH9 : (edge_u < n_pre)) (PreH10 : (0 <= edge_v)) (PreH11 : (edge_v < n_pre)) (PreH12 : (0 <= root_u)) (PreH13 : (root_u < n_pre)) (PreH14 : (0 <= root_v)) (PreH15 : (root_v < n_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre < INT_MAX)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre < INT_MAX)) (PreH20 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH21 : (KruskalEnv g_low_level_spec )) (PreH22 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH23 : (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) chosen s_after )) (PreH24 : (kruskal_scan_phase g_low_level_spec s_after chosen )) (PreH25 : (union_find_connectivity_matches_state g_low_level_spec s_after repr_of_after )) (PreH26 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s_after )) (PreH27 : (safeExec (kruskal_state_is (s_after)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of_after )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition kruskal_entail_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of_2: (Z -> Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of_2 )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "chosen" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_4 (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> retval_4)
  **  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of_2 )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  EX (out_w: Z)  (out_v: Z)  (out_u: Z)  (uf: Z)  (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (repr_of: (Z -> Z))  (s: St)  (l_u: (@list Z))  (l_v: (@list Z))  (l_w: (@list Z))  (edge_order: (@list Z))  (chosen: Z)  (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of_2: (Z -> Z)) (retval: Z) (PreH1 : ((Zlength (l_w1)) = m_pre)) (PreH2 : ((Zlength (l_v1)) = m_pre)) (PreH3 : ((Zlength (l_u1)) = m_pre)) (PreH4 : (retval <> 0)) (PreH5 : (uf_initial n_pre repr_of_2 )) (PreH6 : (0 <= m_pre)) (PreH7 : (m_pre <= INT_MAX)) (PreH8 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH9 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre < INT_MAX)) (PreH14 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH15 : (KruskalEnv g_low_level_spec )) (PreH16 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH17 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (s: St)  (edge_order: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (after_sorted_edge_of_input (Zlength (l_w1)) orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order 0 0 s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s 0 ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of_2 ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec 0 (@nil Z) (@nil Z) (@nil Z) s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition kruskal_entail_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (repr_of_2: (Z -> Z)) (s_2: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order_2: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < n_pre)) (PreH3 : (retval_2 = (repr_of_2 ((Znth i l_v 0))))) (PreH4 : (0 <= retval)) (PreH5 : (retval < n_pre)) (PreH6 : (retval = (repr_of_2 ((Znth i l_u 0))))) (PreH7 : (chosen < (n_pre - 1 ))) (PreH8 : (i < m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= chosen)) (PreH12 : (chosen <= (n_pre - 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre < INT_MAX)) (PreH17 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH18 : (KruskalEnv g_low_level_spec )) (PreH19 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order_2 )) (PreH20 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s_2 )) (PreH21 : (kruskal_scan_phase g_low_level_spec s_2 chosen )) (PreH22 : (union_find_connectivity_matches_state g_low_level_spec s_2 repr_of_2 )) (PreH23 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_2 )) (PreH24 : (safeExec (kruskal_state_is (s_2)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of_2 )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.seg out_u 0 chosen l_out_u_2 )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v_2 )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w_2 )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  EX (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (s: St)  (edge_order: (@list Z))  (repr_of: (Z -> Z))  (l_w_2: (@list Z))  (l_v_2: (@list Z))  (l_u_2: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (chosen < (n_pre - 1 )) ” 
  &&  “ ((Znth i l_u 0) = (Znth i l_u_2 0)) ” 
  &&  “ ((Znth i l_v 0) = (Znth i l_v_2 0)) ” 
  &&  “ ((Znth i l_w 0) = (Znth i l_w_2 0)) ” 
  &&  “ (0 <= (Znth i l_u 0)) ” 
  &&  “ ((Znth i l_u 0) < n_pre) ” 
  &&  “ (0 <= (Znth i l_v 0)) ” 
  &&  “ ((Znth i l_v 0) < n_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < n_pre) ” 
  &&  “ (retval = (repr_of ((Znth i l_u 0)))) ” 
  &&  “ (retval_2 = (repr_of ((Znth i l_v 0)))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (repr_of_2: (Z -> Z)) (s_2: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order_2: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 < n_pre)) (PreH3 : (retval_2 = (repr_of_2 ((Znth i l_v 0))))) (PreH4 : (0 <= retval)) (PreH5 : (retval < n_pre)) (PreH6 : (retval = (repr_of_2 ((Znth i l_u 0))))) (PreH7 : (chosen < (n_pre - 1 ))) (PreH8 : (i < m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= chosen)) (PreH12 : (chosen <= (n_pre - 1 ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre < INT_MAX)) (PreH15 : (1 <= m_pre)) (PreH16 : (m_pre < INT_MAX)) (PreH17 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH18 : (KruskalEnv g_low_level_spec )) (PreH19 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order_2 )) (PreH20 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s_2 )) (PreH21 : (kruskal_scan_phase g_low_level_spec s_2 chosen )) (PreH22 : (union_find_connectivity_matches_state g_low_level_spec s_2 repr_of_2 )) (PreH23 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_2 )) (PreH24 : (safeExec (kruskal_state_is (s_2)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (s: St)  (edge_order: (@list Z)) ,
  “ (0 <= (Znth i l_u 0)) ” 
  &&  “ ((Znth i l_u 0) < n_pre) ” 
  &&  “ (0 <= (Znth i l_v 0)) ” 
  &&  “ ((Znth i l_v 0) < n_pre) ” 
  &&  “ ((repr_of_2 ((Znth i l_u 0))) = (repr_of_2 ((Znth i l_u 0)))) ” 
  &&  “ ((repr_of_2 ((Znth i l_v 0))) = (repr_of_2 ((Znth i l_v 0)))) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of_2 ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition kruskal_entail_wit_3 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s_2: St) (repr_of_2: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (repr_of1_2: (Z -> Z)) (PreH1 : (uf_merge n_pre repr_of_2 edge_u edge_v repr_of1_2 )) (PreH2 : (root_u <> root_v)) (PreH3 : (0 <= i)) (PreH4 : (i < m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (chosen < (n_pre - 1 ))) (PreH8 : (edge_u = (Znth i l_u_2 0))) (PreH9 : (edge_v = (Znth i l_v_2 0))) (PreH10 : (edge_w = (Znth i l_w_2 0))) (PreH11 : (0 <= edge_u)) (PreH12 : (edge_u < n_pre)) (PreH13 : (0 <= edge_v)) (PreH14 : (edge_v < n_pre)) (PreH15 : (0 <= root_u)) (PreH16 : (root_u < n_pre)) (PreH17 : (0 <= root_v)) (PreH18 : (root_v < n_pre)) (PreH19 : (root_u = (repr_of_2 (edge_u)))) (PreH20 : (root_v = (repr_of_2 (edge_v)))) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : (1 <= m_pre)) (PreH24 : (m_pre < INT_MAX)) (PreH25 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH26 : (KruskalEnv g_low_level_spec )) (PreH27 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH28 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s_2 )) (PreH29 : (kruskal_scan_phase g_low_level_spec s_2 chosen )) (PreH30 : (union_find_connectivity_matches_state g_low_level_spec s_2 repr_of_2 )) (PreH31 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_2 )) (PreH32 : (safeExec (kruskal_state_is (s_2)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of1_2 )
  **  (IntArray.seg out_w 0 (chosen + 1 ) (app (l_out_w_2) ((cons (edge_w) ((@nil Z))))) )
  **  (IntArray.undef_seg out_w (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 (chosen + 1 ) (app (l_out_v_2) ((cons (edge_v) ((@nil Z))))) )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u_2) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
|--
  EX (l_out_u1: (@list Z))  (l_out_v1: (@list Z))  (l_out_w1: (@list Z))  (repr_of1: (Z -> Z))  (s_next: St)  (e: Z)  (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (s: St)  (edge_order: (@list Z))  (repr_of: (Z -> Z))  (l_w: (@list Z))  (l_v: (@list Z))  (l_u: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (1 <= (chosen + 1 )) ” 
  &&  “ ((chosen + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (root_u <> root_v) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (root_u = (repr_of (edge_u))) ” 
  &&  “ (root_v = (repr_of (edge_v))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i ((chosen + 1 ) - 1 ) s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s ((chosen + 1 ) - 1 ) ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec ((chosen + 1 ) - 1 ) l_out_u l_out_v l_out_w s ) ” 
  &&  “ (uf_different_class repr_of edge_u edge_v ) ” 
  &&  “ (selected_edge_is_min_edge g_low_level_spec edge_order i s e ) ” 
  &&  “ (selected_edge_pair g_low_level_spec e edge_u edge_v ) ” 
  &&  “ (selected_edge_add_to_mst s s_next edge_u edge_v e ) ” 
  &&  “ (uf_merge n_pre repr_of edge_u edge_v repr_of1 ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) (chosen + 1 ) s_next ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s_next (chosen + 1 ) ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s_next repr_of1 ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec (chosen + 1 ) l_out_u1 l_out_v1 l_out_w1 s_next ) ” 
  &&  “ (safeExec (kruskal_state_is (s_next)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of1 )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 (chosen + 1 ) l_out_u1 )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 (chosen + 1 ) l_out_v1 )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 (chosen + 1 ) l_out_w1 )
  **  (IntArray.undef_seg out_w (chosen + 1 ) (n_pre - 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s_2: St) (repr_of_2: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (repr_of1_2: (Z -> Z)) (PreH1 : (uf_merge n_pre repr_of_2 edge_u edge_v repr_of1_2 )) (PreH2 : (root_u <> root_v)) (PreH3 : (0 <= i)) (PreH4 : (i < m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (chosen < (n_pre - 1 ))) (PreH8 : (edge_u = (Znth i l_u_2 0))) (PreH9 : (edge_v = (Znth i l_v_2 0))) (PreH10 : (edge_w = (Znth i l_w_2 0))) (PreH11 : (0 <= edge_u)) (PreH12 : (edge_u < n_pre)) (PreH13 : (0 <= edge_v)) (PreH14 : (edge_v < n_pre)) (PreH15 : (0 <= root_u)) (PreH16 : (root_u < n_pre)) (PreH17 : (0 <= root_v)) (PreH18 : (root_v < n_pre)) (PreH19 : (root_u = (repr_of_2 (edge_u)))) (PreH20 : (root_v = (repr_of_2 (edge_v)))) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : (1 <= m_pre)) (PreH24 : (m_pre < INT_MAX)) (PreH25 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH26 : (KruskalEnv g_low_level_spec )) (PreH27 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH28 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s_2 )) (PreH29 : (kruskal_scan_phase g_low_level_spec s_2 chosen )) (PreH30 : (union_find_connectivity_matches_state g_low_level_spec s_2 repr_of_2 )) (PreH31 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_2 )) (PreH32 : (safeExec (kruskal_state_is (s_2)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (s_next: St)  (e: Z)  (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (s: St)  (edge_order: (@list Z))  (repr_of: (Z -> Z)) ,
  “ (1 <= (chosen + 1 )) ” 
  &&  “ ((chosen + 1 ) <= (n_pre - 1 )) ” 
  &&  “ ((repr_of_2 (edge_u)) = (repr_of ((Znth i l_u_2 0)))) ” 
  &&  “ ((repr_of_2 (edge_v)) = (repr_of ((Znth i l_v_2 0)))) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i ((chosen + 1 ) - 1 ) s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s ((chosen + 1 ) - 1 ) ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec ((chosen + 1 ) - 1 ) l_out_u l_out_v l_out_w s ) ” 
  &&  “ (uf_different_class repr_of (Znth i l_u_2 0) (Znth i l_v_2 0) ) ” 
  &&  “ (selected_edge_is_min_edge g_low_level_spec edge_order i s e ) ” 
  &&  “ (selected_edge_pair g_low_level_spec e (Znth i l_u_2 0) (Znth i l_v_2 0) ) ” 
  &&  “ (selected_edge_add_to_mst s s_next (Znth i l_u_2 0) (Znth i l_v_2 0) e ) ” 
  &&  “ (uf_merge n_pre repr_of (Znth i l_u_2 0) (Znth i l_v_2 0) repr_of1_2 ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) (chosen + 1 ) s_next ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s_next (chosen + 1 ) ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s_next repr_of1_2 ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec (chosen + 1 ) (app (l_out_u_2) ((cons ((Znth i l_u_2 0)) ((@nil Z))))) (app (l_out_v_2) ((cons ((Znth i l_v_2 0)) ((@nil Z))))) (app (l_out_w_2) ((cons ((Znth i l_w_2 0)) ((@nil Z))))) s_next ) ” 
  &&  “ (safeExec (kruskal_state_is (s_next)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition kruskal_entail_wit_4 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s_2: St) (repr_of_2: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (root_u = root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u_2 0))) (PreH8 : (edge_v = (Znth i l_v_2 0))) (PreH9 : (edge_w = (Znth i l_w_2 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of_2 (edge_u)))) (PreH19 : (root_v = (repr_of_2 (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s_2 )) (PreH28 : (kruskal_scan_phase g_low_level_spec s_2 chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s_2 repr_of_2 )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_2 )) (PreH31 : (safeExec (kruskal_state_is (s_2)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of_2 )
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  (IntArray.seg out_u 0 chosen l_out_u_2 )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v_2 )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w_2 )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  EX (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (s: St)  (edge_order: (@list Z))  (repr_of: (Z -> Z))  (l_w: (@list Z))  (l_v: (@list Z))  (l_u: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (root_u = root_v) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (root_u = (repr_of (edge_u))) ” 
  &&  “ (root_v = (repr_of (edge_v))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (uf_same_class repr_of edge_u edge_v ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) chosen s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s_2: St) (repr_of_2: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (PreH1 : (root_u = root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u_2 0))) (PreH8 : (edge_v = (Znth i l_v_2 0))) (PreH9 : (edge_w = (Znth i l_w_2 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of_2 (edge_u)))) (PreH19 : (root_v = (repr_of_2 (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s_2 )) (PreH28 : (kruskal_scan_phase g_low_level_spec s_2 chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s_2 repr_of_2 )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_2 )) (PreH31 : (safeExec (kruskal_state_is (s_2)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (s: St)  (edge_order: (@list Z)) ,
  “ ((repr_of_2 (edge_v)) = (repr_of_2 ((Znth i l_u_2 0)))) ” 
  &&  “ ((repr_of_2 (edge_v)) = (repr_of_2 ((Znth i l_v_2 0)))) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of_2 ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s ) ” 
  &&  “ (uf_same_class repr_of_2 (Znth i l_u_2 0) (Znth i l_v_2 0) ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) chosen s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition kruskal_entail_wit_5_1 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (l_out_u1: (@list Z)) (l_out_v1: (@list Z)) (l_out_w1: (@list Z)) (s: St) (s_next: St) (repr_of: (Z -> Z)) (repr_of1: (Z -> Z)) (e: Z) (i: Z) (chosen: Z) (root_u: Z) (root_v: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (0 <= i)) (PreH2 : (i < m_pre)) (PreH3 : (1 <= chosen)) (PreH4 : (chosen <= (n_pre - 1 ))) (PreH5 : (root_u <> root_v)) (PreH6 : (edge_u = (Znth i l_u_2 0))) (PreH7 : (edge_v = (Znth i l_v_2 0))) (PreH8 : (edge_w = (Znth i l_w_2 0))) (PreH9 : (0 <= edge_u)) (PreH10 : (edge_u < n_pre)) (PreH11 : (0 <= edge_v)) (PreH12 : (edge_v < n_pre)) (PreH13 : (0 <= root_u)) (PreH14 : (root_u < n_pre)) (PreH15 : (0 <= root_v)) (PreH16 : (root_v < n_pre)) (PreH17 : (root_u = (repr_of (edge_u)))) (PreH18 : (root_v = (repr_of (edge_v)))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (1 <= m_pre)) (PreH22 : (m_pre < INT_MAX)) (PreH23 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH24 : (KruskalEnv g_low_level_spec )) (PreH25 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH26 : (kruskal_scan_state g_low_level_spec edge_order_2 i (chosen - 1 ) s )) (PreH27 : (kruskal_scan_phase g_low_level_spec s (chosen - 1 ) )) (PreH28 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH29 : (output_prefix_matches_state g_low_level_spec (chosen - 1 ) l_out_u_2 l_out_v_2 l_out_w_2 s )) (PreH30 : (uf_different_class repr_of edge_u edge_v )) (PreH31 : (selected_edge_is_min_edge g_low_level_spec edge_order_2 i s e )) (PreH32 : (selected_edge_pair g_low_level_spec e edge_u edge_v )) (PreH33 : (selected_edge_add_to_mst s s_next edge_u edge_v e )) (PreH34 : (uf_merge n_pre repr_of edge_u edge_v repr_of1 )) (PreH35 : (kruskal_scan_state g_low_level_spec edge_order_2 (i + 1 ) chosen s_next )) (PreH36 : (kruskal_scan_phase g_low_level_spec s_next chosen )) (PreH37 : (union_find_connectivity_matches_state g_low_level_spec s_next repr_of1 )) (PreH38 : (output_prefix_matches_state g_low_level_spec chosen l_out_u1 l_out_v1 l_out_w1 s_next )) (PreH39 : (safeExec (kruskal_state_is (s_next)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of1 )
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  (IntArray.seg out_u 0 chosen l_out_u1 )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v1 )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w1 )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  EX (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (repr_of_after: (Z -> Z))  (s_after: St)  (edge_order: (@list Z))  (l_w: (@list Z))  (l_v: (@list Z))  (l_u: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) chosen s_after ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s_after chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s_after repr_of_after ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s_after ) ” 
  &&  “ (safeExec (kruskal_state_is (s_after)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of_after )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (l_out_u1: (@list Z)) (l_out_v1: (@list Z)) (l_out_w1: (@list Z)) (s: St) (s_next: St) (repr_of: (Z -> Z)) (repr_of1: (Z -> Z)) (e: Z) (i: Z) (chosen: Z) (root_u: Z) (root_v: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (PreH1 : (0 <= i)) (PreH2 : (i < m_pre)) (PreH3 : (1 <= chosen)) (PreH4 : (chosen <= (n_pre - 1 ))) (PreH5 : (root_u <> root_v)) (PreH6 : (edge_u = (Znth i l_u_2 0))) (PreH7 : (edge_v = (Znth i l_v_2 0))) (PreH8 : (edge_w = (Znth i l_w_2 0))) (PreH9 : (0 <= edge_u)) (PreH10 : (edge_u < n_pre)) (PreH11 : (0 <= edge_v)) (PreH12 : (edge_v < n_pre)) (PreH13 : (0 <= root_u)) (PreH14 : (root_u < n_pre)) (PreH15 : (0 <= root_v)) (PreH16 : (root_v < n_pre)) (PreH17 : (root_u = (repr_of (edge_u)))) (PreH18 : (root_v = (repr_of (edge_v)))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (1 <= m_pre)) (PreH22 : (m_pre < INT_MAX)) (PreH23 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH24 : (KruskalEnv g_low_level_spec )) (PreH25 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH26 : (kruskal_scan_state g_low_level_spec edge_order_2 i (chosen - 1 ) s )) (PreH27 : (kruskal_scan_phase g_low_level_spec s (chosen - 1 ) )) (PreH28 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH29 : (output_prefix_matches_state g_low_level_spec (chosen - 1 ) l_out_u_2 l_out_v_2 l_out_w_2 s )) (PreH30 : (uf_different_class repr_of edge_u edge_v )) (PreH31 : (selected_edge_is_min_edge g_low_level_spec edge_order_2 i s e )) (PreH32 : (selected_edge_pair g_low_level_spec e edge_u edge_v )) (PreH33 : (selected_edge_add_to_mst s s_next edge_u edge_v e )) (PreH34 : (uf_merge n_pre repr_of edge_u edge_v repr_of1 )) (PreH35 : (kruskal_scan_state g_low_level_spec edge_order_2 (i + 1 ) chosen s_next )) (PreH36 : (kruskal_scan_phase g_low_level_spec s_next chosen )) (PreH37 : (union_find_connectivity_matches_state g_low_level_spec s_next repr_of1 )) (PreH38 : (output_prefix_matches_state g_low_level_spec chosen l_out_u1 l_out_v1 l_out_w1 s_next )) (PreH39 : (safeExec (kruskal_state_is (s_next)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (s_after: St)  (edge_order: (@list Z)) ,
  “ (0 <= chosen) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) chosen s_after ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s_after chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s_after repr_of1 ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u1 l_out_v1 l_out_w1 s_after ) ” 
  &&  “ (safeExec (kruskal_state_is (s_after)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition kruskal_entail_wit_5_2 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (root_u: Z) (root_v: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (0 <= i)) (PreH2 : (i < m_pre)) (PreH3 : (0 <= chosen)) (PreH4 : (chosen <= (n_pre - 1 ))) (PreH5 : (root_u = root_v)) (PreH6 : (edge_u = (Znth i l_u_2 0))) (PreH7 : (edge_v = (Znth i l_v_2 0))) (PreH8 : (edge_w = (Znth i l_w_2 0))) (PreH9 : (0 <= edge_u)) (PreH10 : (edge_u < n_pre)) (PreH11 : (0 <= edge_v)) (PreH12 : (edge_v < n_pre)) (PreH13 : (0 <= root_u)) (PreH14 : (root_u < n_pre)) (PreH15 : (0 <= root_v)) (PreH16 : (root_v < n_pre)) (PreH17 : (root_u = (repr_of (edge_u)))) (PreH18 : (root_v = (repr_of (edge_v)))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (1 <= m_pre)) (PreH22 : (m_pre < INT_MAX)) (PreH23 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH24 : (KruskalEnv g_low_level_spec )) (PreH25 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH26 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s )) (PreH27 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH28 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH29 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s )) (PreH30 : (uf_same_class repr_of edge_u edge_v )) (PreH31 : (kruskal_scan_state g_low_level_spec edge_order_2 (i + 1 ) chosen s )) (PreH32 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  (IntArray.seg out_u 0 chosen l_out_u_2 )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v_2 )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w_2 )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  EX (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (repr_of_after: (Z -> Z))  (s_after: St)  (edge_order: (@list Z))  (l_w: (@list Z))  (l_v: (@list Z))  (l_u: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) chosen s_after ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s_after chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s_after repr_of_after ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s_after ) ” 
  &&  “ (safeExec (kruskal_state_is (s_after)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of_after )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (root_u: Z) (root_v: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (PreH1 : (0 <= i)) (PreH2 : (i < m_pre)) (PreH3 : (0 <= chosen)) (PreH4 : (chosen <= (n_pre - 1 ))) (PreH5 : (root_u = root_v)) (PreH6 : (edge_u = (Znth i l_u_2 0))) (PreH7 : (edge_v = (Znth i l_v_2 0))) (PreH8 : (edge_w = (Znth i l_w_2 0))) (PreH9 : (0 <= edge_u)) (PreH10 : (edge_u < n_pre)) (PreH11 : (0 <= edge_v)) (PreH12 : (edge_v < n_pre)) (PreH13 : (0 <= root_u)) (PreH14 : (root_u < n_pre)) (PreH15 : (0 <= root_v)) (PreH16 : (root_v < n_pre)) (PreH17 : (root_u = (repr_of (edge_u)))) (PreH18 : (root_v = (repr_of (edge_v)))) (PreH19 : (2 <= n_pre)) (PreH20 : (n_pre < INT_MAX)) (PreH21 : (1 <= m_pre)) (PreH22 : (m_pre < INT_MAX)) (PreH23 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH24 : (KruskalEnv g_low_level_spec )) (PreH25 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH26 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s )) (PreH27 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH28 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH29 : (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s )) (PreH30 : (uf_same_class repr_of edge_u edge_v )) (PreH31 : (kruskal_scan_state g_low_level_spec edge_order_2 (i + 1 ) chosen s )) (PreH32 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (s_after: St)  (edge_order: (@list Z)) ,
  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i + 1 ) chosen s_after ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s_after chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s_after repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u_2 l_out_v_2 l_out_w_2 s_after ) ” 
  &&  “ (safeExec (kruskal_state_is (s_after)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition kruskal_entail_wit_6 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s_after: St) (repr_of_after: (Z -> Z)) (i_2: Z) (chosen_2: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf_2: Z) (out_u_2: Z) (out_v_2: Z) (out_w_2: Z) (PreH1 : (0 <= i_2)) (PreH2 : (i_2 < m_pre)) (PreH3 : (0 <= chosen_2)) (PreH4 : (chosen_2 <= (n_pre - 1 ))) (PreH5 : (edge_u = (Znth i_2 l_u_2 0))) (PreH6 : (edge_v = (Znth i_2 l_v_2 0))) (PreH7 : (edge_w = (Znth i_2 l_w_2 0))) (PreH8 : (0 <= edge_u)) (PreH9 : (edge_u < n_pre)) (PreH10 : (0 <= edge_v)) (PreH11 : (edge_v < n_pre)) (PreH12 : (0 <= root_u)) (PreH13 : (root_u < n_pre)) (PreH14 : (0 <= root_v)) (PreH15 : (root_v < n_pre)) (PreH16 : (2 <= n_pre)) (PreH17 : (n_pre < INT_MAX)) (PreH18 : (1 <= m_pre)) (PreH19 : (m_pre < INT_MAX)) (PreH20 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH21 : (KruskalEnv g_low_level_spec )) (PreH22 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH23 : (kruskal_scan_state g_low_level_spec edge_order_2 (i_2 + 1 ) chosen_2 s_after )) (PreH24 : (kruskal_scan_phase g_low_level_spec s_after chosen_2 )) (PreH25 : (union_find_connectivity_matches_state g_low_level_spec s_after repr_of_after )) (PreH26 : (output_prefix_matches_state g_low_level_spec chosen_2 l_out_u_2 l_out_v_2 l_out_w_2 s_after )) (PreH27 : (safeExec (kruskal_state_is (s_after)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen_2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf_2)
  **  (UF uf_2 n_pre repr_of_after )
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u_2)
  **  (IntArray.seg out_u_2 0 chosen_2 l_out_u_2 )
  **  (IntArray.undef_seg out_u_2 chosen_2 (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v_2)
  **  (IntArray.seg out_v_2 0 chosen_2 l_out_v_2 )
  **  (IntArray.undef_seg out_v_2 chosen_2 (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w_2)
  **  (IntArray.seg out_w_2 0 chosen_2 l_out_w_2 )
  **  (IntArray.undef_seg out_w_2 chosen_2 (n_pre - 1 ) )
|--
  EX (out_w: Z)  (out_v: Z)  (out_u: Z)  (uf: Z)  (l_out_u: (@list Z))  (l_out_v: (@list Z))  (l_out_w: (@list Z))  (repr_of: (Z -> Z))  (s: St)  (l_u: (@list Z))  (l_v: (@list Z))  (l_w: (@list Z))  (edge_order: (@list Z))  (chosen: Z)  (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (l_out_u_2: (@list Z)) (l_out_v_2: (@list Z)) (l_out_w_2: (@list Z)) (s_after: St) (repr_of_after: (Z -> Z)) (i_2: Z) (chosen_2: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (PreH1 : ((Zlength (l_out_w_2)) = (chosen_2 - 0 ))) (PreH2 : ((Zlength (l_out_v_2)) = (chosen_2 - 0 ))) (PreH3 : ((Zlength (l_out_u_2)) = (chosen_2 - 0 ))) (PreH4 : ((Zlength (l_w_2)) = m_pre)) (PreH5 : ((Zlength (l_v_2)) = m_pre)) (PreH6 : ((Zlength (l_u_2)) = m_pre)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < m_pre)) (PreH9 : (0 <= chosen_2)) (PreH10 : (chosen_2 <= (n_pre - 1 ))) (PreH11 : (edge_u = (Znth i_2 l_u_2 0))) (PreH12 : (edge_v = (Znth i_2 l_v_2 0))) (PreH13 : (edge_w = (Znth i_2 l_w_2 0))) (PreH14 : (0 <= edge_u)) (PreH15 : (edge_u < n_pre)) (PreH16 : (0 <= edge_v)) (PreH17 : (edge_v < n_pre)) (PreH18 : (0 <= root_u)) (PreH19 : (root_u < n_pre)) (PreH20 : (0 <= root_v)) (PreH21 : (root_v < n_pre)) (PreH22 : (2 <= n_pre)) (PreH23 : (n_pre < INT_MAX)) (PreH24 : (1 <= m_pre)) (PreH25 : (m_pre < INT_MAX)) (PreH26 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH27 : (KruskalEnv g_low_level_spec )) (PreH28 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH29 : (kruskal_scan_state g_low_level_spec edge_order_2 (i_2 + 1 ) chosen_2 s_after )) (PreH30 : (kruskal_scan_phase g_low_level_spec s_after chosen_2 )) (PreH31 : (union_find_connectivity_matches_state g_low_level_spec s_after repr_of_after )) (PreH32 : (output_prefix_matches_state g_low_level_spec chosen_2 l_out_u_2 l_out_v_2 l_out_w_2 s_after )) (PreH33 : (safeExec (kruskal_state_is (s_after)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (s: St)  (edge_order: (@list Z)) ,
  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= (Zlength (l_w_2))) ” 
  &&  “ (after_sorted_edge_of_input (Zlength (l_w_2)) orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order (i_2 + 1 ) chosen_2 s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen_2 ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of_after ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen_2 l_out_u_2 l_out_v_2 l_out_w_2 s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition kruskal_return_wit_1 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((&((retval)  # "mst_tree" ->ₛ "ru")) # Ptr  |-> out_u)
  **  ((&((retval)  # "mst_tree" ->ₛ "rv")) # Ptr  |-> out_v)
  **  ((&((retval)  # "mst_tree" ->ₛ "rw")) # Ptr  |-> out_w)
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  EX (retval_rw: Z)  (retval_rv: Z)  (retval_ru: Z)  (lru: (@list Z))  (lrv: (@list Z))  (lrw: (@list Z))  (l_u: (@list Z))  (l_v: (@list Z))  (l_w: (@list Z))  (edge_order: (@list Z))  (rg: G) ,
  “ (safeExec (kruskal_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_result_graph_matches_array lru lrv lrw g_low_level_spec rg ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((&((retval)  # "mst_tree" ->ₛ "ru")) # Ptr  |-> retval_ru)
  **  (IntArray.full retval_ru (n_pre - 1 ) lru )
  **  ((&((retval)  # "mst_tree" ->ₛ "rv")) # Ptr  |-> retval_rv)
  **  (IntArray.full retval_rv (n_pre - 1 ) lrv )
  **  ((&((retval)  # "mst_tree" ->ₛ "rw")) # Ptr  |-> retval_rw)
  **  (IntArray.full retval_rw (n_pre - 1 ) lrw )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (i >= m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  EX (lru: (@list Z))  (lrv: (@list Z))  (lrw: (@list Z))  (edge_order: (@list Z))  (rg: G) ,
  “ (safeExec (kruskal_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order ) ” 
  &&  “ (kruskal_result_graph_matches_array lru lrv lrw g_low_level_spec rg ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full out_u (n_pre - 1 ) lru )
  **  (IntArray.full out_v (n_pre - 1 ) lrv )
  **  (IntArray.full out_w (n_pre - 1 ) lrw )
).

Definition kruskal_return_wit_2 := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (chosen >= (n_pre - 1 ))) (PreH3 : (i < m_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= m_pre)) (PreH6 : (0 <= chosen)) (PreH7 : (chosen <= (n_pre - 1 ))) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre < INT_MAX)) (PreH12 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH13 : (KruskalEnv g_low_level_spec )) (PreH14 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH15 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s )) (PreH16 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH17 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH18 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH19 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((&((retval)  # "mst_tree" ->ₛ "ru")) # Ptr  |-> out_u)
  **  ((&((retval)  # "mst_tree" ->ₛ "rv")) # Ptr  |-> out_v)
  **  ((&((retval)  # "mst_tree" ->ₛ "rw")) # Ptr  |-> out_w)
  **  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.seg out_w 0 chosen l_out_w )
|--
  EX (retval_rw: Z)  (retval_rv: Z)  (retval_ru: Z)  (lru: (@list Z))  (lrv: (@list Z))  (lrw: (@list Z))  (l_u: (@list Z))  (l_v: (@list Z))  (l_w: (@list Z))  (edge_order: (@list Z))  (rg: G) ,
  “ (safeExec (kruskal_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_result_graph_matches_array lru lrv lrw g_low_level_spec rg ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((&((retval)  # "mst_tree" ->ₛ "ru")) # Ptr  |-> retval_ru)
  **  (IntArray.full retval_ru (n_pre - 1 ) lru )
  **  ((&((retval)  # "mst_tree" ->ₛ "rv")) # Ptr  |-> retval_rv)
  **  (IntArray.full retval_rv (n_pre - 1 ) lrv )
  **  ((&((retval)  # "mst_tree" ->ₛ "rw")) # Ptr  |-> retval_rw)
  **  (IntArray.full retval_rw (n_pre - 1 ) lrw )
) \/
(
forall (m_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u_2: (@list Z)) (l_v_2: (@list Z)) (l_w_2: (@list Z)) (edge_order_2: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (chosen >= (n_pre - 1 ))) (PreH3 : (i < m_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= m_pre)) (PreH6 : (0 <= chosen)) (PreH7 : (chosen <= (n_pre - 1 ))) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre < INT_MAX)) (PreH10 : (1 <= m_pre)) (PreH11 : (m_pre < INT_MAX)) (PreH12 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH13 : (KruskalEnv g_low_level_spec )) (PreH14 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 )) (PreH15 : (kruskal_scan_state g_low_level_spec edge_order_2 i chosen s )) (PreH16 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH17 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH18 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH19 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  EX (rg: G) ,
  “ (safeExec (kruskal_state_graph_matches (rg)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (kruskal_result_graph_matches_array l_out_u l_out_v l_out_w g_low_level_spec rg ) ”
  &&  emp
).

Definition kruskal_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre < INT_MAX)) (PreH5 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH6 : (KruskalEnv g_low_level_spec )) (PreH7 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH8 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  (IntArray.full u_pre m_pre orig_u_low_level_spec )
  **  (IntArray.full v_pre m_pre orig_v_low_level_spec )
  **  (IntArray.full w_pre m_pre orig_w_low_level_spec )
|--
  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ”
.

Definition kruskal_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre < INT_MAX)) (PreH5 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH6 : (KruskalEnv g_low_level_spec )) (PreH7 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH8 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full u_pre m_pre orig_u_low_level_spec )
  **  (IntArray.full v_pre m_pre orig_v_low_level_spec )
  **  (IntArray.full w_pre m_pre orig_w_low_level_spec )
|--
  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full u_pre m_pre orig_u_low_level_spec )
  **  (IntArray.full v_pre m_pre orig_v_low_level_spec )
  **  (IntArray.full w_pre m_pre orig_w_low_level_spec )
.

Definition kruskal_partial_solve_wit_1 := kruskal_partial_solve_wit_1_pure -> kruskal_partial_solve_wit_1_aux.

Definition kruskal_partial_solve_wit_2_pure := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (PreH1 : (0 <= m_pre)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH4 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre < INT_MAX)) (PreH9 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH10 : (KruskalEnv g_low_level_spec )) (PreH11 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH12 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "uf" ) )) # Ptr  |->_)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
.

Definition kruskal_partial_solve_wit_2_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (PreH1 : (0 <= m_pre)) (PreH2 : (m_pre <= INT_MAX)) (PreH3 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH4 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH5 : (2 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (1 <= m_pre)) (PreH8 : (m_pre < INT_MAX)) (PreH9 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH10 : (KruskalEnv g_low_level_spec )) (PreH11 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH12 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
|--
  “ (0 < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation (Zrange (0) (m_pre)) edge_order1 ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
.

Definition kruskal_partial_solve_wit_2 := kruskal_partial_solve_wit_2_pure -> kruskal_partial_solve_wit_2_aux.

Definition kruskal_partial_solve_wit_3_pure := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_u" ) )) # Ptr  |->_)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ ((n_pre - 1 ) > 0) ”
.

Definition kruskal_partial_solve_wit_3_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF retval n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
|--
  “ ((n_pre - 1 ) > 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (uf_initial n_pre repr_of ) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation (Zrange (0) (m_pre)) edge_order1 ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF retval n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
.

Definition kruskal_partial_solve_wit_3 := kruskal_partial_solve_wit_3_pure -> kruskal_partial_solve_wit_3_aux.

Definition kruskal_partial_solve_wit_4_pure := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_v" ) )) # Ptr  |->_)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ ((n_pre - 1 ) > 0) ”
.

Definition kruskal_partial_solve_wit_4_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  (UF retval n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
|--
  “ ((n_pre - 1 ) > 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (uf_initial n_pre repr_of ) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation (Zrange (0) (m_pre)) edge_order1 ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  (UF retval n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
.

Definition kruskal_partial_solve_wit_4 := kruskal_partial_solve_wit_4_pure -> kruskal_partial_solve_wit_4_aux.

Definition kruskal_partial_solve_wit_5_pure := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out_w" ) )) # Ptr  |->_)
  **  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> retval_3)
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  ((( &( "out_u" ) )) # Ptr  |-> retval_2)
  **  (UF retval n_pre repr_of )
  **  ((( &( "uf" ) )) # Ptr  |-> retval)
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
|--
  “ ((n_pre - 1 ) > 0) ”
.

Definition kruskal_partial_solve_wit_5_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u1: (@list Z)) (l_v1: (@list Z)) (l_w1: (@list Z)) (edge_order1: (@list Z)) (repr_of: (Z -> Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval <> 0)) (PreH2 : (uf_initial n_pre repr_of )) (PreH3 : (0 <= m_pre)) (PreH4 : (m_pre <= INT_MAX)) (PreH5 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 )) (PreH6 : (Permutation (Zrange (0) (m_pre)) edge_order1 )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) )) (PreH14 : (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  (UF retval n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
|--
  “ ((n_pre - 1 ) > 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (uf_initial n_pre repr_of ) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (m_pre <= INT_MAX) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u1 l_v1 l_w1 edge_order1 ) ” 
  &&  “ (Permutation (Zrange (0) (m_pre)) edge_order1 ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.undef_full retval_3 (n_pre - 1 ) )
  **  (IntArray.undef_full retval_2 (n_pre - 1 ) )
  **  (UF retval n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u1 )
  **  (IntArray.full v_pre m_pre l_v1 )
  **  (IntArray.full w_pre m_pre l_w1 )
.

Definition kruskal_partial_solve_wit_5 := kruskal_partial_solve_wit_5_pure -> kruskal_partial_solve_wit_5_aux.

Definition kruskal_partial_solve_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (chosen < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((u_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l_u 0))
  **  (IntArray.missing_i u_pre i 0 m_pre l_u )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (chosen < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full u_pre m_pre l_u )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((v_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l_v 0))
  **  (IntArray.missing_i v_pre i 0 m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (chosen < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((w_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l_w 0))
  **  (IntArray.missing_i w_pre i 0 m_pre l_w )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (UF uf n_pre repr_of )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_9_pure := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (chosen < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_u" ) )) # Int  |->_)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((Znth i l_u 0) < n_pre) ” 
  &&  “ (0 <= (Znth i l_u 0)) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (chosen <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : ((Znth i l_u 0) <= INT_MAX)) (PreH6 : ((Znth i l_v 0) <= INT_MAX)) (PreH7 : ((Znth i l_w 0) <= INT_MAX)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (chosen >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((Znth i l_u 0) >= INT_MIN)) (PreH13 : ((Znth i l_v 0) >= INT_MIN)) (PreH14 : ((Znth i l_w 0) >= INT_MIN)) (PreH15 : (chosen < (n_pre - 1 ))) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (0 <= chosen)) (PreH20 : (chosen <= (n_pre - 1 ))) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : (1 <= m_pre)) (PreH24 : (m_pre < INT_MAX)) (PreH25 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH26 : (KruskalEnv g_low_level_spec )) (PreH27 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH28 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH29 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH30 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH31 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH32 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_u" ) )) # Int  |->_)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (0 <= (Znth i l_u 0)) ” 
  &&  “ ((Znth i l_u 0) < n_pre) ”
).

Definition kruskal_partial_solve_wit_9_pure_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (chosen <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : ((Znth i l_u 0) <= INT_MAX)) (PreH6 : ((Znth i l_v 0) <= INT_MAX)) (PreH7 : ((Znth i l_w 0) <= INT_MAX)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (chosen >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((Znth i l_u 0) >= INT_MIN)) (PreH13 : ((Znth i l_v 0) >= INT_MIN)) (PreH14 : ((Znth i l_w 0) >= INT_MIN)) (PreH15 : (chosen < (n_pre - 1 ))) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (0 <= chosen)) (PreH20 : (chosen <= (n_pre - 1 ))) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : (1 <= m_pre)) (PreH24 : (m_pre < INT_MAX)) (PreH25 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH26 : (KruskalEnv g_low_level_spec )) (PreH27 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH28 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH29 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH30 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH31 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH32 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_u" ) )) # Int  |->_)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (0 <= (Znth i l_u 0)) ”
.

Definition kruskal_partial_solve_wit_9_pure_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (chosen <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : ((Znth i l_u 0) <= INT_MAX)) (PreH6 : ((Znth i l_v 0) <= INT_MAX)) (PreH7 : ((Znth i l_w 0) <= INT_MAX)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (chosen >= INT_MIN)) (PreH10 : (m_pre >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : ((Znth i l_u 0) >= INT_MIN)) (PreH13 : ((Znth i l_v 0) >= INT_MIN)) (PreH14 : ((Znth i l_w 0) >= INT_MIN)) (PreH15 : (chosen < (n_pre - 1 ))) (PreH16 : (i < m_pre)) (PreH17 : (0 <= i)) (PreH18 : (i <= m_pre)) (PreH19 : (0 <= chosen)) (PreH20 : (chosen <= (n_pre - 1 ))) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre < INT_MAX)) (PreH23 : (1 <= m_pre)) (PreH24 : (m_pre < INT_MAX)) (PreH25 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH26 : (KruskalEnv g_low_level_spec )) (PreH27 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH28 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH29 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH30 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH31 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH32 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_u" ) )) # Int  |->_)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((Znth i l_u 0) < n_pre) ”
.

Definition kruskal_partial_solve_wit_9_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (chosen < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (UF uf n_pre repr_of )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((Znth i l_u 0) < n_pre) ” 
  &&  “ (0 <= (Znth i l_u 0)) ” 
  &&  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_9 := kruskal_partial_solve_wit_9_pure -> kruskal_partial_solve_wit_9_aux.

Definition kruskal_partial_solve_wit_10_pure := 
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < n_pre)) (PreH3 : (retval = (repr_of ((Znth i l_u 0))))) (PreH4 : (chosen < (n_pre - 1 ))) (PreH5 : (i < m_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= m_pre)) (PreH8 : (0 <= chosen)) (PreH9 : (chosen <= (n_pre - 1 ))) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre < INT_MAX)) (PreH14 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH15 : (KruskalEnv g_low_level_spec )) (PreH16 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH17 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH18 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH19 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH20 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH21 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_v" ) )) # Int  |->_)
  **  (UF uf n_pre repr_of )
  **  ((( &( "root_u" ) )) # Int  |-> retval)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((Znth i l_v 0) < n_pre) ” 
  &&  “ (0 <= (Znth i l_v 0)) ”
) \/
(
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (chosen <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : ((Znth i l_u 0) <= INT_MAX)) (PreH6 : ((Znth i l_v 0) <= INT_MAX)) (PreH7 : ((Znth i l_w 0) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (chosen >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : ((Znth i l_u 0) >= INT_MIN)) (PreH14 : ((Znth i l_v 0) >= INT_MIN)) (PreH15 : ((Znth i l_w 0) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (0 <= retval)) (PreH18 : (retval < n_pre)) (PreH19 : (retval = (repr_of ((Znth i l_u 0))))) (PreH20 : (chosen < (n_pre - 1 ))) (PreH21 : (i < m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= m_pre)) (PreH24 : (0 <= chosen)) (PreH25 : (chosen <= (n_pre - 1 ))) (PreH26 : (2 <= n_pre)) (PreH27 : (n_pre < INT_MAX)) (PreH28 : (1 <= m_pre)) (PreH29 : (m_pre < INT_MAX)) (PreH30 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH31 : (KruskalEnv g_low_level_spec )) (PreH32 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH33 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH34 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH35 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH36 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH37 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_v" ) )) # Int  |->_)
  **  (UF uf n_pre repr_of )
  **  ((( &( "root_u" ) )) # Int  |-> retval)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (0 <= (Znth i l_v 0)) ” 
  &&  “ ((Znth i l_v 0) < n_pre) ”
).

Definition kruskal_partial_solve_wit_10_pure_split_goal_1 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (chosen <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : ((Znth i l_u 0) <= INT_MAX)) (PreH6 : ((Znth i l_v 0) <= INT_MAX)) (PreH7 : ((Znth i l_w 0) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (chosen >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : ((Znth i l_u 0) >= INT_MIN)) (PreH14 : ((Znth i l_v 0) >= INT_MIN)) (PreH15 : ((Znth i l_w 0) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (0 <= retval)) (PreH18 : (retval < n_pre)) (PreH19 : (retval = (repr_of ((Znth i l_u 0))))) (PreH20 : (chosen < (n_pre - 1 ))) (PreH21 : (i < m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= m_pre)) (PreH24 : (0 <= chosen)) (PreH25 : (chosen <= (n_pre - 1 ))) (PreH26 : (2 <= n_pre)) (PreH27 : (n_pre < INT_MAX)) (PreH28 : (1 <= m_pre)) (PreH29 : (m_pre < INT_MAX)) (PreH30 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH31 : (KruskalEnv g_low_level_spec )) (PreH32 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH33 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH34 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH35 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH36 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH37 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_v" ) )) # Int  |->_)
  **  (UF uf n_pre repr_of )
  **  ((( &( "root_u" ) )) # Int  |-> retval)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (0 <= (Znth i l_v 0)) ”
.

Definition kruskal_partial_solve_wit_10_pure_split_goal_2 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (chosen <= INT_MAX)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : ((Znth i l_u 0) <= INT_MAX)) (PreH6 : ((Znth i l_v 0) <= INT_MAX)) (PreH7 : ((Znth i l_w 0) <= INT_MAX)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (chosen >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : ((Znth i l_u 0) >= INT_MIN)) (PreH14 : ((Znth i l_v 0) >= INT_MIN)) (PreH15 : ((Znth i l_w 0) >= INT_MIN)) (PreH16 : (retval >= INT_MIN)) (PreH17 : (0 <= retval)) (PreH18 : (retval < n_pre)) (PreH19 : (retval = (repr_of ((Znth i l_u 0))))) (PreH20 : (chosen < (n_pre - 1 ))) (PreH21 : (i < m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i <= m_pre)) (PreH24 : (0 <= chosen)) (PreH25 : (chosen <= (n_pre - 1 ))) (PreH26 : (2 <= n_pre)) (PreH27 : (n_pre < INT_MAX)) (PreH28 : (1 <= m_pre)) (PreH29 : (m_pre < INT_MAX)) (PreH30 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH31 : (KruskalEnv g_low_level_spec )) (PreH32 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH33 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH34 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH35 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH36 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH37 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  ((( &( "root_v" ) )) # Int  |->_)
  **  (UF uf n_pre repr_of )
  **  ((( &( "root_u" ) )) # Int  |-> retval)
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "edge_w" ) )) # Int  |-> (Znth i l_w 0))
  **  (IntArray.full v_pre m_pre l_v )
  **  ((( &( "edge_v" ) )) # Int  |-> (Znth i l_v 0))
  **  (IntArray.full u_pre m_pre l_u )
  **  ((( &( "edge_u" ) )) # Int  |-> (Znth i l_u 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> chosen)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((Znth i l_v 0) < n_pre) ”
.

Definition kruskal_partial_solve_wit_10_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < n_pre)) (PreH3 : (retval = (repr_of ((Znth i l_u 0))))) (PreH4 : (chosen < (n_pre - 1 ))) (PreH5 : (i < m_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= m_pre)) (PreH8 : (0 <= chosen)) (PreH9 : (chosen <= (n_pre - 1 ))) (PreH10 : (2 <= n_pre)) (PreH11 : (n_pre < INT_MAX)) (PreH12 : (1 <= m_pre)) (PreH13 : (m_pre < INT_MAX)) (PreH14 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH15 : (KruskalEnv g_low_level_spec )) (PreH16 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH17 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH18 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH19 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH20 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH21 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ ((Znth i l_v 0) < n_pre) ” 
  &&  “ (0 <= (Znth i l_v 0)) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ (retval = (repr_of ((Znth i l_u 0)))) ” 
  &&  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_10 := kruskal_partial_solve_wit_10_pure -> kruskal_partial_solve_wit_10_aux.

Definition kruskal_partial_solve_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (root_u <> root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u 0))) (PreH8 : (edge_v = (Znth i l_v 0))) (PreH9 : (edge_w = (Znth i l_w 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of (edge_u)))) (PreH19 : (root_v = (repr_of (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH28 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH31 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (root_u <> root_v) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (root_u = (repr_of (edge_u))) ” 
  &&  “ (root_v = (repr_of (edge_v))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((out_u + (chosen * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (root_u <> root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u 0))) (PreH8 : (edge_v = (Znth i l_v 0))) (PreH9 : (edge_w = (Znth i l_w 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of (edge_u)))) (PreH19 : (root_v = (repr_of (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH28 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH31 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (root_u <> root_v) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (root_u = (repr_of (edge_u))) ” 
  &&  “ (root_v = (repr_of (edge_v))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((out_v + (chosen * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (root_u <> root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u 0))) (PreH8 : (edge_v = (Znth i l_v 0))) (PreH9 : (edge_w = (Znth i l_w 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of (edge_u)))) (PreH19 : (root_v = (repr_of (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH28 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH31 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg out_v 0 (chosen + 1 ) (app (l_out_v) ((cons (edge_v) ((@nil Z))))) )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (root_u <> root_v) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (root_u = (repr_of (edge_u))) ” 
  &&  “ (root_v = (repr_of (edge_v))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (((out_w + (chosen * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_w (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 (chosen + 1 ) (app (l_out_v) ((cons (edge_v) ((@nil Z))))) )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_w 0 chosen l_out_w )
.

Definition kruskal_partial_solve_wit_14_pure := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (root_u <> root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u 0))) (PreH8 : (edge_v = (Znth i l_v 0))) (PreH9 : (edge_w = (Znth i l_w 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of (edge_u)))) (PreH19 : (root_v = (repr_of (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH28 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH31 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg out_w 0 (chosen + 1 ) (app (l_out_w) ((cons (edge_w) ((@nil Z))))) )
  **  (IntArray.undef_seg out_w (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 (chosen + 1 ) (app (l_out_v) ((cons (edge_v) ((@nil Z))))) )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "chosen" ) )) # Int  |-> (chosen + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "edge_u" ) )) # Int  |-> edge_u)
  **  ((( &( "edge_v" ) )) # Int  |-> edge_v)
  **  ((( &( "edge_w" ) )) # Int  |-> edge_w)
  **  ((( &( "root_u" ) )) # Int  |-> root_u)
  **  ((( &( "root_v" ) )) # Int  |-> root_v)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "w" ) )) # Ptr  |-> w_pre)
  **  ((( &( "uf" ) )) # Ptr  |-> uf)
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((( &( "out_u" ) )) # Ptr  |-> out_u)
  **  ((( &( "out_v" ) )) # Ptr  |-> out_v)
  **  ((( &( "out_w" ) )) # Ptr  |-> out_w)
|--
  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ”
.

Definition kruskal_partial_solve_wit_14_aux := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (s: St) (repr_of: (Z -> Z)) (i: Z) (chosen: Z) (edge_u: Z) (edge_v: Z) (edge_w: Z) (root_u: Z) (root_v: Z) (uf: Z) (out_u: Z) (out_v: Z) (out_w: Z) (PreH1 : (root_u <> root_v)) (PreH2 : (0 <= i)) (PreH3 : (i < m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (chosen < (n_pre - 1 ))) (PreH7 : (edge_u = (Znth i l_u 0))) (PreH8 : (edge_v = (Znth i l_v 0))) (PreH9 : (edge_w = (Znth i l_w 0))) (PreH10 : (0 <= edge_u)) (PreH11 : (edge_u < n_pre)) (PreH12 : (0 <= edge_v)) (PreH13 : (edge_v < n_pre)) (PreH14 : (0 <= root_u)) (PreH15 : (root_u < n_pre)) (PreH16 : (0 <= root_v)) (PreH17 : (root_v < n_pre)) (PreH18 : (root_u = (repr_of (edge_u)))) (PreH19 : (root_v = (repr_of (edge_v)))) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre < INT_MAX)) (PreH22 : (1 <= m_pre)) (PreH23 : (m_pre < INT_MAX)) (PreH24 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH25 : (KruskalEnv g_low_level_spec )) (PreH26 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH27 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH28 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH29 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH30 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH31 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.seg out_w 0 (chosen + 1 ) (app (l_out_w) ((cons (edge_w) ((@nil Z))))) )
  **  (IntArray.undef_seg out_w (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 (chosen + 1 ) (app (l_out_v) ((cons (edge_v) ((@nil Z))))) )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
|--
  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (root_u <> root_v) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (chosen < (n_pre - 1 )) ” 
  &&  “ (edge_u = (Znth i l_u 0)) ” 
  &&  “ (edge_v = (Znth i l_v 0)) ” 
  &&  “ (edge_w = (Znth i l_w 0)) ” 
  &&  “ (0 <= edge_u) ” 
  &&  “ (edge_u < n_pre) ” 
  &&  “ (0 <= edge_v) ” 
  &&  “ (edge_v < n_pre) ” 
  &&  “ (0 <= root_u) ” 
  &&  “ (root_u < n_pre) ” 
  &&  “ (0 <= root_v) ” 
  &&  “ (root_v < n_pre) ” 
  &&  “ (root_u = (repr_of (edge_u))) ” 
  &&  “ (root_v = (repr_of (edge_v))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of )
  **  (IntArray.seg out_w 0 (chosen + 1 ) (app (l_out_w) ((cons (edge_w) ((@nil Z))))) )
  **  (IntArray.undef_seg out_w (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 (chosen + 1 ) (app (l_out_v) ((cons (edge_v) ((@nil Z))))) )
  **  (IntArray.undef_seg out_v (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.seg out_u 0 (chosen + 1 ) (app (l_out_u) ((cons (edge_u) ((@nil Z))))) )
  **  (IntArray.undef_seg out_u (chosen + 1 ) (n_pre - 1 ) )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
.

Definition kruskal_partial_solve_wit_14 := kruskal_partial_solve_wit_14_pure -> kruskal_partial_solve_wit_14_aux.

Definition kruskal_partial_solve_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre < INT_MAX)) (PreH10 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH11 : (KruskalEnv g_low_level_spec )) (PreH12 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH13 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH14 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH15 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH16 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH17 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (i >= m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (uf: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (chosen >= (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (chosen >= (n_pre - 1 )) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (UF uf n_pre repr_of )
  **  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.seg out_w 0 chosen l_out_w )
.

Definition kruskal_partial_solve_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (0 <= chosen)) (PreH5 : (chosen <= (n_pre - 1 ))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre < INT_MAX)) (PreH8 : (1 <= m_pre)) (PreH9 : (m_pre < INT_MAX)) (PreH10 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH11 : (KruskalEnv g_low_level_spec )) (PreH12 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH13 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH14 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH15 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH16 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH17 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
|--
  “ (i >= m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.undef_seg out_u chosen (n_pre - 1 ) )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.undef_seg out_v chosen (n_pre - 1 ) )
  **  (IntArray.seg out_w 0 chosen l_out_w )
  **  (IntArray.undef_seg out_w chosen (n_pre - 1 ) )
.

Definition kruskal_partial_solve_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (X_low_level_spec: (unit -> (St -> Prop))) (g_low_level_spec: G) (orig_w_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_u_low_level_spec: (@list Z)) (out_w: Z) (out_v: Z) (out_u: Z) (l_out_u: (@list Z)) (l_out_v: (@list Z)) (l_out_w: (@list Z)) (repr_of: (Z -> Z)) (s: St) (l_u: (@list Z)) (l_v: (@list Z)) (l_w: (@list Z)) (edge_order: (@list Z)) (chosen: Z) (i: Z) (PreH1 : (chosen >= (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= m_pre)) (PreH5 : (0 <= chosen)) (PreH6 : (chosen <= (n_pre - 1 ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre < INT_MAX)) (PreH9 : (1 <= m_pre)) (PreH10 : (m_pre < INT_MAX)) (PreH11 : (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec )) (PreH12 : (KruskalEnv g_low_level_spec )) (PreH13 : (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order )) (PreH14 : (kruskal_scan_state g_low_level_spec edge_order i chosen s )) (PreH15 : (kruskal_scan_phase g_low_level_spec s chosen )) (PreH16 : (union_find_connectivity_matches_state g_low_level_spec s repr_of )) (PreH17 : (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s )) (PreH18 : (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec )) ,
  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.seg out_w 0 chosen l_out_w )
|--
  “ (chosen >= (n_pre - 1 )) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= m_pre) ” 
  &&  “ (0 <= chosen) ” 
  &&  “ (chosen <= (n_pre - 1 )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_scan_state g_low_level_spec edge_order i chosen s ) ” 
  &&  “ (kruskal_scan_phase g_low_level_spec s chosen ) ” 
  &&  “ (union_find_connectivity_matches_state g_low_level_spec s repr_of ) ” 
  &&  “ (output_prefix_matches_state g_low_level_spec chosen l_out_u l_out_v l_out_w s ) ” 
  &&  “ (safeExec (kruskal_state_is (s)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  (IntArray.seg out_u 0 chosen l_out_u )
  **  (IntArray.seg out_v 0 chosen l_out_v )
  **  (IntArray.seg out_w 0 chosen l_out_w )
.

Definition kruskal_derive_high_level_spec_by_low_level_spec := 
forall (m_pre: Z) (n_pre: Z) (w_pre: Z) (v_pre: Z) (u_pre: Z) (g_high_level_spec: G) (orig_w_high_level_spec: (@list Z)) (orig_v_high_level_spec: (@list Z)) (orig_u_high_level_spec: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_high_level_spec orig_v_high_level_spec orig_w_high_level_spec g_high_level_spec ) ” 
  &&  “ (KruskalEnv g_high_level_spec ) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_high_level_spec orig_v_high_level_spec orig_w_high_level_spec orig_u_high_level_spec orig_v_high_level_spec orig_w_high_level_spec (Zrange (0) (m_pre)) ) ”
  &&  (IntArray.full u_pre m_pre orig_u_high_level_spec )
  **  (IntArray.full v_pre m_pre orig_v_high_level_spec )
  **  (IntArray.full w_pre m_pre orig_w_high_level_spec )
|--
EX (orig_u_low_level_spec: (@list Z)) (orig_v_low_level_spec: (@list Z)) (orig_w_low_level_spec: (@list Z)) (g_low_level_spec: G) (X_low_level_spec: (unit -> (St -> Prop))) ,
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre < INT_MAX) ” 
  &&  “ (array_graph n_pre m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec g_low_level_spec ) ” 
  &&  “ (KruskalEnv g_low_level_spec ) ” 
  &&  “ (edge_arrays_ordered_by m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec (Zrange (0) (m_pre)) ) ” 
  &&  “ (safeExec (initStPred (g_low_level_spec)) (KruskalProg (g_low_level_spec)) X_low_level_spec ) ”
  &&  (IntArray.full u_pre m_pre orig_u_low_level_spec )
  **  (IntArray.full v_pre m_pre orig_v_low_level_spec )
  **  (IntArray.full w_pre m_pre orig_w_low_level_spec ))
  **
  ((EX retval_rw_2 retval_rv_2 retval_ru_2 lru_2 lrv_2 lrw_2 l_u_2 l_v_2 l_w_2 edge_order_2 rg_2 retval_2,
  “ (safeExec (kruskal_state_graph_matches (rg_2)) (return (tt)) X_low_level_spec ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_low_level_spec orig_v_low_level_spec orig_w_low_level_spec l_u_2 l_v_2 l_w_2 edge_order_2 ) ” 
  &&  “ (kruskal_result_graph_matches_array lru_2 lrv_2 lrw_2 g_low_level_spec rg_2 ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (IntArray.full u_pre m_pre l_u_2 )
  **  (IntArray.full v_pre m_pre l_v_2 )
  **  (IntArray.full w_pre m_pre l_w_2 )
  **  ((&((retval_2)  # "mst_tree" ->ₛ "ru")) # Ptr  |-> retval_ru_2)
  **  (IntArray.full retval_ru_2 (n_pre - 1 ) lru_2 )
  **  ((&((retval_2)  # "mst_tree" ->ₛ "rv")) # Ptr  |-> retval_rv_2)
  **  (IntArray.full retval_rv_2 (n_pre - 1 ) lrv_2 )
  **  ((&((retval_2)  # "mst_tree" ->ₛ "rw")) # Ptr  |-> retval_rw_2)
  **  (IntArray.full retval_rw_2 (n_pre - 1 ) lrw_2 ))
  -*
  (EX retval_rw retval_rv retval_ru lru lrv lrw l_u l_v l_w edge_order rg retval,
  “ (return_is_mst g_high_level_spec rg ) ” 
  &&  “ (after_sorted_edge_of_input m_pre orig_u_high_level_spec orig_v_high_level_spec orig_w_high_level_spec l_u l_v l_w edge_order ) ” 
  &&  “ (kruskal_result_graph_matches_array lru lrv lrw g_high_level_spec rg ) ” 
  &&  “ (retval <> 0) ”
  &&  (IntArray.full u_pre m_pre l_u )
  **  (IntArray.full v_pre m_pre l_v )
  **  (IntArray.full w_pre m_pre l_w )
  **  ((&((retval)  # "mst_tree" ->ₛ "ru")) # Ptr  |-> retval_ru)
  **  (IntArray.full retval_ru (n_pre - 1 ) lru )
  **  ((&((retval)  # "mst_tree" ->ₛ "rv")) # Ptr  |-> retval_rv)
  **  (IntArray.full retval_rv (n_pre - 1 ) lrv )
  **  ((&((retval)  # "mst_tree" ->ₛ "rw")) # Ptr  |-> retval_rw)
  **  (IntArray.full retval_rw (n_pre - 1 ) lrw )))
.

Module Type VC_Correct.

Include safeexec_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_swap_int_return_wit_1 : swap_int_return_wit_1.
Axiom proof_of_swap_edge_entail_wit_1 : swap_edge_entail_wit_1.
Axiom proof_of_swap_edge_entail_wit_2 : swap_edge_entail_wit_2.
Axiom proof_of_swap_edge_return_wit_1 : swap_edge_return_wit_1.
Axiom proof_of_swap_edge_return_wit_2 : swap_edge_return_wit_2.
Axiom proof_of_swap_edge_return_wit_3 : swap_edge_return_wit_3.
Axiom proof_of_swap_edge_partial_solve_wit_1_pure : swap_edge_partial_solve_wit_1_pure.
Axiom proof_of_swap_edge_partial_solve_wit_1 : swap_edge_partial_solve_wit_1.
Axiom proof_of_swap_edge_partial_solve_wit_2_pure : swap_edge_partial_solve_wit_2_pure.
Axiom proof_of_swap_edge_partial_solve_wit_2 : swap_edge_partial_solve_wit_2.
Axiom proof_of_swap_edge_partial_solve_wit_3_pure : swap_edge_partial_solve_wit_3_pure.
Axiom proof_of_swap_edge_partial_solve_wit_3 : swap_edge_partial_solve_wit_3.
Axiom proof_of_swap_edge_partial_solve_wit_4_pure : swap_edge_partial_solve_wit_4_pure.
Axiom proof_of_swap_edge_partial_solve_wit_4 : swap_edge_partial_solve_wit_4.
Axiom proof_of_swap_edge_partial_solve_wit_5_pure : swap_edge_partial_solve_wit_5_pure.
Axiom proof_of_swap_edge_partial_solve_wit_5 : swap_edge_partial_solve_wit_5.
Axiom proof_of_swap_edge_partial_solve_wit_6_pure : swap_edge_partial_solve_wit_6_pure.
Axiom proof_of_swap_edge_partial_solve_wit_6 : swap_edge_partial_solve_wit_6.
Axiom proof_of_partitionByWeight_safety_wit_1 : partitionByWeight_safety_wit_1.
Axiom proof_of_partitionByWeight_safety_wit_2 : partitionByWeight_safety_wit_2.
Axiom proof_of_partitionByWeight_safety_wit_3 : partitionByWeight_safety_wit_3.
Axiom proof_of_partitionByWeight_entail_wit_1 : partitionByWeight_entail_wit_1.
Axiom proof_of_partitionByWeight_entail_wit_2_1 : partitionByWeight_entail_wit_2_1.
Axiom proof_of_partitionByWeight_entail_wit_2_2 : partitionByWeight_entail_wit_2_2.
Axiom proof_of_partitionByWeight_return_wit_1 : partitionByWeight_return_wit_1.
Axiom proof_of_partitionByWeight_partial_solve_wit_1 : partitionByWeight_partial_solve_wit_1.
Axiom proof_of_partitionByWeight_partial_solve_wit_2 : partitionByWeight_partial_solve_wit_2.
Axiom proof_of_partitionByWeight_partial_solve_wit_3_pure : partitionByWeight_partial_solve_wit_3_pure.
Axiom proof_of_partitionByWeight_partial_solve_wit_3 : partitionByWeight_partial_solve_wit_3.
Axiom proof_of_partitionByWeight_partial_solve_wit_4_pure : partitionByWeight_partial_solve_wit_4_pure.
Axiom proof_of_partitionByWeight_partial_solve_wit_4 : partitionByWeight_partial_solve_wit_4.
Axiom proof_of_quickByWeightRange_safety_wit_1 : quickByWeightRange_safety_wit_1.
Axiom proof_of_quickByWeightRange_safety_wit_2 : quickByWeightRange_safety_wit_2.
Axiom proof_of_quickByWeightRange_safety_wit_3 : quickByWeightRange_safety_wit_3.
Axiom proof_of_quickByWeightRange_safety_wit_4 : quickByWeightRange_safety_wit_4.
Axiom proof_of_quickByWeightRange_return_wit_1 : quickByWeightRange_return_wit_1.
Axiom proof_of_quickByWeightRange_return_wit_2 : quickByWeightRange_return_wit_2.
Axiom proof_of_quickByWeightRange_partial_solve_wit_1_pure : quickByWeightRange_partial_solve_wit_1_pure.
Axiom proof_of_quickByWeightRange_partial_solve_wit_1 : quickByWeightRange_partial_solve_wit_1.
Axiom proof_of_quickByWeightRange_partial_solve_wit_2_pure : quickByWeightRange_partial_solve_wit_2_pure.
Axiom proof_of_quickByWeightRange_partial_solve_wit_2 : quickByWeightRange_partial_solve_wit_2.
Axiom proof_of_quickByWeightRange_partial_solve_wit_3_pure : quickByWeightRange_partial_solve_wit_3_pure.
Axiom proof_of_quickByWeightRange_partial_solve_wit_3 : quickByWeightRange_partial_solve_wit_3.
Axiom proof_of_quickByWeight_safety_wit_1 : quickByWeight_safety_wit_1.
Axiom proof_of_quickByWeight_safety_wit_2 : quickByWeight_safety_wit_2.
Axiom proof_of_quickByWeight_safety_wit_3 : quickByWeight_safety_wit_3.
Axiom proof_of_quickByWeight_safety_wit_4 : quickByWeight_safety_wit_4.
Axiom proof_of_quickByWeight_return_wit_1 : quickByWeight_return_wit_1.
Axiom proof_of_quickByWeight_return_wit_2 : quickByWeight_return_wit_2.
Axiom proof_of_quickByWeight_partial_solve_wit_1_pure : quickByWeight_partial_solve_wit_1_pure.
Axiom proof_of_quickByWeight_partial_solve_wit_1 : quickByWeight_partial_solve_wit_1.
Axiom proof_of_kruskal_safety_wit_1 : kruskal_safety_wit_1.
Axiom proof_of_kruskal_safety_wit_2 : kruskal_safety_wit_2.
Axiom proof_of_kruskal_safety_wit_3 : kruskal_safety_wit_3.
Axiom proof_of_kruskal_safety_wit_4 : kruskal_safety_wit_4.
Axiom proof_of_kruskal_safety_wit_5 : kruskal_safety_wit_5.
Axiom proof_of_kruskal_safety_wit_6 : kruskal_safety_wit_6.
Axiom proof_of_kruskal_safety_wit_7 : kruskal_safety_wit_7.
Axiom proof_of_kruskal_safety_wit_8 : kruskal_safety_wit_8.
Axiom proof_of_kruskal_safety_wit_9 : kruskal_safety_wit_9.
Axiom proof_of_kruskal_safety_wit_10 : kruskal_safety_wit_10.
Axiom proof_of_kruskal_safety_wit_11 : kruskal_safety_wit_11.
Axiom proof_of_kruskal_safety_wit_12 : kruskal_safety_wit_12.
Axiom proof_of_kruskal_entail_wit_1 : kruskal_entail_wit_1.
Axiom proof_of_kruskal_entail_wit_2 : kruskal_entail_wit_2.
Axiom proof_of_kruskal_entail_wit_3 : kruskal_entail_wit_3.
Axiom proof_of_kruskal_entail_wit_4 : kruskal_entail_wit_4.
Axiom proof_of_kruskal_entail_wit_5_1 : kruskal_entail_wit_5_1.
Axiom proof_of_kruskal_entail_wit_5_2 : kruskal_entail_wit_5_2.
Axiom proof_of_kruskal_entail_wit_6 : kruskal_entail_wit_6.
Axiom proof_of_kruskal_return_wit_1 : kruskal_return_wit_1.
Axiom proof_of_kruskal_return_wit_2 : kruskal_return_wit_2.
Axiom proof_of_kruskal_partial_solve_wit_1_pure : kruskal_partial_solve_wit_1_pure.
Axiom proof_of_kruskal_partial_solve_wit_1 : kruskal_partial_solve_wit_1.
Axiom proof_of_kruskal_partial_solve_wit_2_pure : kruskal_partial_solve_wit_2_pure.
Axiom proof_of_kruskal_partial_solve_wit_2 : kruskal_partial_solve_wit_2.
Axiom proof_of_kruskal_partial_solve_wit_3_pure : kruskal_partial_solve_wit_3_pure.
Axiom proof_of_kruskal_partial_solve_wit_3 : kruskal_partial_solve_wit_3.
Axiom proof_of_kruskal_partial_solve_wit_4_pure : kruskal_partial_solve_wit_4_pure.
Axiom proof_of_kruskal_partial_solve_wit_4 : kruskal_partial_solve_wit_4.
Axiom proof_of_kruskal_partial_solve_wit_5_pure : kruskal_partial_solve_wit_5_pure.
Axiom proof_of_kruskal_partial_solve_wit_5 : kruskal_partial_solve_wit_5.
Axiom proof_of_kruskal_partial_solve_wit_6 : kruskal_partial_solve_wit_6.
Axiom proof_of_kruskal_partial_solve_wit_7 : kruskal_partial_solve_wit_7.
Axiom proof_of_kruskal_partial_solve_wit_8 : kruskal_partial_solve_wit_8.
Axiom proof_of_kruskal_partial_solve_wit_9_pure : kruskal_partial_solve_wit_9_pure.
Axiom proof_of_kruskal_partial_solve_wit_9 : kruskal_partial_solve_wit_9.
Axiom proof_of_kruskal_partial_solve_wit_10_pure : kruskal_partial_solve_wit_10_pure.
Axiom proof_of_kruskal_partial_solve_wit_10 : kruskal_partial_solve_wit_10.
Axiom proof_of_kruskal_partial_solve_wit_11 : kruskal_partial_solve_wit_11.
Axiom proof_of_kruskal_partial_solve_wit_12 : kruskal_partial_solve_wit_12.
Axiom proof_of_kruskal_partial_solve_wit_13 : kruskal_partial_solve_wit_13.
Axiom proof_of_kruskal_partial_solve_wit_14_pure : kruskal_partial_solve_wit_14_pure.
Axiom proof_of_kruskal_partial_solve_wit_14 : kruskal_partial_solve_wit_14.
Axiom proof_of_kruskal_partial_solve_wit_15 : kruskal_partial_solve_wit_15.
Axiom proof_of_kruskal_partial_solve_wit_16 : kruskal_partial_solve_wit_16.
Axiom proof_of_kruskal_partial_solve_wit_17 : kruskal_partial_solve_wit_17.
Axiom proof_of_kruskal_partial_solve_wit_18 : kruskal_partial_solve_wit_18.
Axiom proof_of_kruskal_derive_high_level_spec_by_low_level_spec : kruskal_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
