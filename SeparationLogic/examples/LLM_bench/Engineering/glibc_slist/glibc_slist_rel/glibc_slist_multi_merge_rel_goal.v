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
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import glibc_slist_multi_merge_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_multi_merge -----*)

Definition glibc_slist_clean_multi_merge_safety_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_2 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> y_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_3 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> y_pre)
  **  ((( &( "y" ) )) # Ptr  |-> 0)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_4 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_5 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_6 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre = 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> z_pre)
  **  ((( &( "y" ) )) # Ptr  |-> 0)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_7 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> y_pre)
  **  ((( &( "y" ) )) # Ptr  |-> 0)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_8 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  ((( &( "take_y" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH2 : (cursor <> 0)) (PreH3 : (y_pre <> 0)) (PreH4 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_10 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH2 : (cursor <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_11 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH3 : (cursor <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_12 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH3 : (cursor <> 0)) (PreH4 : (y_pre <> 0)) (PreH5 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_13 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty <> 0)) (PreH2 : (z <> 0)) (PreH3 : (y = 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty <> 0)) (PreH2 : (z <> 0)) (PreH3 : (y = 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (y_pre <> 0)) (PreH7 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_15 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty <> 0)) (PreH2 : (y <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (y_pre <> 0)) (PreH6 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_16 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty <> 0)) (PreH2 : (y <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_17 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_18 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (y_pre <> 0)) (PreH8 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_19 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (ty <> 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (y_pre <> 0)) (PreH7 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_20 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (ty <> 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_21 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty = 0)) (PreH2 : (z <> 0)) (PreH3 : (y = 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_22 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty = 0)) (PreH2 : (z <> 0)) (PreH3 : (y = 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (y_pre <> 0)) (PreH7 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_23 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty = 0)) (PreH2 : (y <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (y_pre <> 0)) (PreH6 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_24 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (ty = 0)) (PreH2 : (y <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_25 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (ty <> 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (y_pre <> 0)) (PreH8 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_26 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (ty <> 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_27 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (ty = 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_28 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (ty = 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (y_pre <> 0)) (PreH8 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_29 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (y = 0)) (PreH3 : (ty <> 0)) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH7 : (cursor <> 0)) (PreH8 : (y_pre <> 0)) (PreH9 : (x_pre = 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_30 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (y = 0)) (PreH3 : (ty <> 0)) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH7 : (cursor <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (x_pre <> 0)) ,
  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_31 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (y <> 0)) (PreH5 : (ty <> 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_32 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (y <> 0)) (PreH5 : (ty <> 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (y_pre <> 0)) (PreH10 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_33 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (z <> 0)) (PreH7 : (y = 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_34 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (z <> 0)) (PreH7 : (y = 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_35 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (y_pre <> 0)) (PreH10 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_36 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_37 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (ty <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (y_pre <> 0)) (PreH12 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_38 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (ty <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (x_pre <> 0)) (PreH12 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_39 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (z = 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (y_pre <> 0)) (PreH10 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_40 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (z = 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> ty)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ False ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_41 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (z = 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> 1)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_42 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (z = 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (y_pre <> 0)) (PreH10 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> 1)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_43 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (ty <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (x_pre <> 0)) (PreH12 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> 0)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_44 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (ty <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (y_pre <> 0)) (PreH12 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> 0)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_45 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> 1)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_46 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (y_pre <> 0)) (PreH10 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> 1)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_47 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (z <> 0)) (PreH7 : (y = 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> 1)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_48 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty = 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l4 = (cons (x_2) (l0)))) (PreH4 : (z <> 0)) (PreH5 : (ty = 0)) (PreH6 : (z <> 0)) (PreH7 : (y = 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> z)
  **  ((( &( "take_y" ) )) # Int  |-> 1)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
  **  ((( &( "z" ) )) # Ptr  |-> y_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_49 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (y <> 0)) (PreH5 : (ty <> 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (y_pre <> 0)) (PreH10 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> 0)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_safety_wit_50 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (ty <> 0)) (PreH2 : (l2 = (cons (x_3) (l0_2)))) (PreH3 : (l3 = (cons (x_2) (l0)))) (PreH4 : (y <> 0)) (PreH5 : (ty <> 0)) (PreH6 : (y <> 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "take_y" ) )) # Int  |-> 0)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (sll z l4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_merge_entail_wit_1_1 := 
(
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg y_pre y_pre l1 )
  **  (sll y_pre l2 )
  **  (sll 0 l3 )
  **  (sll z_pre l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop ((@nil Z)) (l2_low_level_spec) ((@nil Z)) (l3_low_level_spec))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (l1_low_level_spec = (@nil Z)) ”
  &&  emp
).

Definition glibc_slist_clean_multi_merge_entail_wit_1_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop ((@nil Z)) (l2_low_level_spec) ((@nil Z)) (l3_low_level_spec))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ”
.

Definition glibc_slist_clean_multi_merge_entail_wit_1_1_split_goal_2 := 
forall (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (l1_low_level_spec = (@nil Z)) ”
.

Definition glibc_slist_clean_multi_merge_entail_wit_1_1_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  TT && emp 
.

Definition glibc_slist_clean_multi_merge_entail_wit_1_2 := 
(
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x_pre x_pre l1_2 )
  **  (sll x_pre l2_2 )
  **  (sll y_pre l3_2 )
  **  (sll z_pre l4_2 )
) \/
(
forall (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop ((@nil Z)) (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_multi_merge_entail_wit_1_2_split_goal_1 := 
forall (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (x_pre <> 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop ((@nil Z)) (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_entail_wit_2_1 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (y_2 <> 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (z = 0)) (PreH6 : (ty = 0)) (PreH7 : (y_3 <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y l0 )
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y_3)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_2 l1_2 )
  **  (sll y_2 l2_2 )
  **  (sll y l3_2 )
  **  (sll z l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_2 <> 0)) (PreH6 : (ty = 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l3_3 = (cons (x_2) (l0)))) (PreH9 : (z = 0)) (PreH10 : (ty = 0)) (PreH11 : (y_3 <> 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l0_2) (l0) ((@nil Z)))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x y_2 l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_2 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (y_2 <> 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (z = 0)) (PreH6 : (ty = 0)) (PreH7 : (y_3 <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y l0 )
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y_3)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_2 l1 )
  **  (sll y_2 l2 )
  **  (sll y l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_2 <> 0)) (PreH6 : (ty = 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l3_3 = (cons (x_2) (l0)))) (PreH9 : (z = 0)) (PreH10 : (ty = 0)) (PreH11 : (y_3 <> 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (y_pre <> 0)) (PreH15 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l0_2) (l0) ((@nil Z)))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x y_2 l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_3 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (y = 0)) (PreH7 : (ty <> 0)) (PreH8 : (z <> 0)) (PreH9 : (y = 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (x_pre <> 0)) (PreH13 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_3 l1_2 )
  **  (sll y_3 l2_2 )
  **  (sll y l3_2 )
  **  (sll y_2 l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_3 <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l4_3 = (cons (x_2) (l0)))) (PreH9 : (z <> 0)) (PreH10 : (y = 0)) (PreH11 : (ty <> 0)) (PreH12 : (z <> 0)) (PreH13 : (y = 0)) (PreH14 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH15 : (cursor <> 0)) (PreH16 : (x_pre <> 0)) (PreH17 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l0_2) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x y_3 l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_4 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (y = 0)) (PreH7 : (ty <> 0)) (PreH8 : (z <> 0)) (PreH9 : (y = 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (y_pre <> 0)) (PreH13 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_3 l1 )
  **  (sll y_3 l2 )
  **  (sll y l3 )
  **  (sll y_2 l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_3 <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l4_3 = (cons (x_2) (l0)))) (PreH9 : (z <> 0)) (PreH10 : (y = 0)) (PreH11 : (ty <> 0)) (PreH12 : (z <> 0)) (PreH13 : (y = 0)) (PreH14 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH15 : (cursor <> 0)) (PreH16 : (y_pre <> 0)) (PreH17 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l0_2) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x y_3 l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_5 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 <> 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_3 l1_2 )
  **  (sll y_3 l2_2 )
  **  (sll y l3_2 )
  **  (sll y_2 l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_3 <> 0)) (PreH6 : (ty = 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l4_3 = (cons (x_2) (l0)))) (PreH9 : (z <> 0)) (PreH10 : (ty = 0)) (PreH11 : (y <> 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l0_2) (l3_3) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x y_3 l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_6 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 <> 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_3 l1 )
  **  (sll y_3 l2 )
  **  (sll y l3 )
  **  (sll y_2 l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_3 <> 0)) (PreH6 : (ty = 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l4_3 = (cons (x_2) (l0)))) (PreH9 : (z <> 0)) (PreH10 : (ty = 0)) (PreH11 : (y <> 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (y_pre <> 0)) (PreH15 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l0_2) (l3_3) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x y_3 l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_7 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 <> 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (y_pre <> 0)) (PreH12 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_3 l1 )
  **  (sll y_3 l2 )
  **  (sll y l3 )
  **  (sll y_2 l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_3 <> 0)) (PreH6 : (ty = 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l4_3 = (cons (x_2) (l0)))) (PreH9 : (z <> 0)) (PreH10 : (ty = 0)) (PreH11 : (z <> 0)) (PreH12 : (y = 0)) (PreH13 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH14 : (cursor <> 0)) (PreH15 : (y_pre <> 0)) (PreH16 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l0_2) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x y_3 l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_8 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 <> 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (x_pre <> 0)) (PreH12 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_3 l1_2 )
  **  (sll y_3 l2_2 )
  **  (sll y l3_2 )
  **  (sll y_2 l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_3 <> 0)) (PreH6 : (ty = 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l4_3 = (cons (x_2) (l0)))) (PreH9 : (z <> 0)) (PreH10 : (ty = 0)) (PreH11 : (z <> 0)) (PreH12 : (y = 0)) (PreH13 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH14 : (cursor <> 0)) (PreH15 : (x_pre <> 0)) (PreH16 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l0_2) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_3 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x y_3 l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_9 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (y_2 <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (y_3 <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (y_3 <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y l0 )
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y_3)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_2 l1 )
  **  (sll y_2 l2 )
  **  (sll y l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_2 <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l3_3 = (cons (x_2) (l0)))) (PreH9 : (y_3 <> 0)) (PreH10 : (ty <> 0)) (PreH11 : (y_3 <> 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (y_pre <> 0)) (PreH15 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l0_2) (l0) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x y_2 l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_10 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (y_2 <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (y_3 <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (y_3 <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y l0 )
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y_3)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y_2 l1_2 )
  **  (sll y_2 l2_2 )
  **  (sll y l3_2 )
  **  (sll z l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y_3: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_3 <= INT_MAX)) (PreH3 : (x_2 >= INT_MIN)) (PreH4 : (x_3 >= INT_MIN)) (PreH5 : (y_2 <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (l2_3 = (cons (x_3) (l0_2)))) (PreH8 : (l3_3 = (cons (x_2) (l0)))) (PreH9 : (y_3 <> 0)) (PreH10 : (ty <> 0)) (PreH11 : (y_3 <> 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l0_2) (l0) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x y_2 l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_11 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (z = 0)) (PreH6 : (ty = 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y l1_2 )
  **  (sll y l2_2 )
  **  (sll y_2 l3_2 )
  **  (sll z l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty = 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l3_3 = (cons (x_2) (l0)))) (PreH7 : (z = 0)) (PreH8 : (ty = 0)) (PreH9 : (y <> 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (x_pre <> 0)) (PreH13 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) ((cons (x_2) ((@nil Z)))) (l0) ((@nil Z)))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x y l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_12 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (z = 0)) (PreH6 : (ty = 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y l1 )
  **  (sll y l2 )
  **  (sll y_2 l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty = 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l3_3 = (cons (x_2) (l0)))) (PreH7 : (z = 0)) (PreH8 : (ty = 0)) (PreH9 : (y <> 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (y_pre <> 0)) (PreH13 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (y <> 0) ” 
  &&  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) ((cons (x_2) ((@nil Z)))) (l0) ((@nil Z)))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x y l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_13 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (y = 0)) (PreH7 : (ty <> 0)) (PreH8 : (z <> 0)) (PreH9 : (y = 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (x_pre <> 0)) (PreH13 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x z l1_2 )
  **  (sll z l2_2 )
  **  (sll y l3_2 )
  **  (sll y_2 l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty <> 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l4_3 = (cons (x_2) (l0)))) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (ty <> 0)) (PreH10 : (z <> 0)) (PreH11 : (y = 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (x_pre <> 0)) (PreH15 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (z <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) ((cons (x_2) ((@nil Z)))) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x z l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_14 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (y = 0)) (PreH7 : (ty <> 0)) (PreH8 : (z <> 0)) (PreH9 : (y = 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (y_pre <> 0)) (PreH13 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x z l1 )
  **  (sll z l2 )
  **  (sll y l3 )
  **  (sll y_2 l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty <> 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l4_3 = (cons (x_2) (l0)))) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (ty <> 0)) (PreH10 : (z <> 0)) (PreH11 : (y = 0)) (PreH12 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH13 : (cursor <> 0)) (PreH14 : (y_pre <> 0)) (PreH15 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (z <> 0) ” 
  &&  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) ((cons (x_2) ((@nil Z)))) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x z l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_15 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x z l1_2 )
  **  (sll z l2_2 )
  **  (sll y l3_2 )
  **  (sll y_2 l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty = 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l4_3 = (cons (x_2) (l0)))) (PreH7 : (z <> 0)) (PreH8 : (ty = 0)) (PreH9 : (y <> 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (x_pre <> 0)) (PreH13 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (z <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) ((cons (x_2) ((@nil Z)))) (l3_3) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x z l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_16 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x z l1 )
  **  (sll z l2 )
  **  (sll y l3 )
  **  (sll y_2 l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty = 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l4_3 = (cons (x_2) (l0)))) (PreH7 : (z <> 0)) (PreH8 : (ty = 0)) (PreH9 : (y <> 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (y_pre <> 0)) (PreH13 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (z <> 0) ” 
  &&  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) ((cons (x_2) ((@nil Z)))) (l3_3) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x z l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_17 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (y_pre <> 0)) (PreH12 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x z l1 )
  **  (sll z l2 )
  **  (sll y l3 )
  **  (sll y_2 l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty = 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l4_3 = (cons (x_2) (l0)))) (PreH7 : (z <> 0)) (PreH8 : (ty = 0)) (PreH9 : (z <> 0)) (PreH10 : (y = 0)) (PreH11 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH12 : (cursor <> 0)) (PreH13 : (y_pre <> 0)) (PreH14 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (z <> 0) ” 
  &&  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) ((cons (x_2) ((@nil Z)))) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x z l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_18 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty = 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l4_3 = (cons (x_2) (l0)))) (PreH5 : (z <> 0)) (PreH6 : (ty = 0)) (PreH7 : (z <> 0)) (PreH8 : (y = 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (x_pre <> 0)) (PreH12 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> z)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x z l1_2 )
  **  (sll z l2_2 )
  **  (sll y l3_2 )
  **  (sll y_2 l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty = 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l4_3 = (cons (x_2) (l0)))) (PreH7 : (z <> 0)) (PreH8 : (ty = 0)) (PreH9 : (z <> 0)) (PreH10 : (y = 0)) (PreH11 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH12 : (cursor <> 0)) (PreH13 : (x_pre <> 0)) (PreH14 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll y l3_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (z <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) ((cons (x_2) ((@nil Z)))) ((@nil Z)) (l0))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (z <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x z l1_2 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_19 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (y <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (y_pre <> 0)) (PreH11 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z))  (l4: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y l1 )
  **  (sll y l2 )
  **  (sll y_2 l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty <> 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l3_3 = (cons (x_2) (l0)))) (PreH7 : (y <> 0)) (PreH8 : (ty <> 0)) (PreH9 : (y <> 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (y_pre <> 0)) (PreH13 : (x_pre = 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z)) ,
  “ (y <> 0) ” 
  &&  “ (l1_low_level_spec = (@nil Z)) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) ((cons (x_2) ((@nil Z)))) (l0) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  (sllseg x y l1 )
).

Definition glibc_slist_clean_multi_merge_entail_wit_2_20 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (ty <> 0)) (PreH3 : (l2_3 = (cons (x_3) (l0_2)))) (PreH4 : (l3_3 = (cons (x_2) (l0)))) (PreH5 : (y <> 0)) (PreH6 : (ty <> 0)) (PreH7 : (y <> 0)) (PreH8 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH9 : (cursor <> 0)) (PreH10 : (x_pre <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  (sllseg x cursor l1_3 )
  **  (sll z l4_3 )
|--
  EX (l1_2: (@list Z))  (l2_2: (@list Z))  (l3_2: (@list Z))  (l4_2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) (l2_2) (l3_2) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg x y l1_2 )
  **  (sll y l2_2 )
  **  (sll y_2 l3_2 )
  **  (sll z l4_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1_3: (@list Z)) (l2_3: (@list Z)) (l3_3: (@list Z)) (l4_3: (@list Z)) (x_2: Z) (l0: (@list Z)) (x_3: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x_3 <= INT_MAX)) (PreH2 : (x_3 >= INT_MIN)) (PreH3 : (y_3 = 0)) (PreH4 : (ty <> 0)) (PreH5 : (l2_3 = (cons (x_3) (l0_2)))) (PreH6 : (l3_3 = (cons (x_2) (l0)))) (PreH7 : (y <> 0)) (PreH8 : (ty <> 0)) (PreH9 : (y <> 0)) (PreH10 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_3) (l2_3) (l3_3) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH11 : (cursor <> 0)) (PreH12 : (x_pre <> 0)) (PreH13 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  (sllseg x cursor l1_3 )
|--
  EX (l1_2: (@list Z)) ,
  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1_2) ((cons (x_2) ((@nil Z)))) (l0) (l4_3))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x y l1_2 )
).

Definition glibc_slist_clean_multi_merge_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4_2: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (y = 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (y_pre <> 0)) (PreH6 : (x_pre = 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4_2 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l4: (@list Z)) ,
  “ (safeExec ATrue (return (l4)) X_low_level_spec ) ”
  &&  (sll x l4 )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4_2: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (y = 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (y_pre <> 0)) (PreH6 : (x_pre = 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4_2 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (l4: (@list Z)) ,
  “ (safeExec ATrue (return (l4)) X_low_level_spec ) ”
  &&  (sll x l4 )
).

Definition glibc_slist_clean_multi_merge_return_wit_2 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4_2: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (y = 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4_2 )
|--
  EX (l4: (@list Z)) ,
  “ (safeExec ATrue (return (l4)) X_low_level_spec ) ”
  &&  (sll x l4 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4_2: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (y = 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4_2))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4_2 )
|--
  EX (l4: (@list Z)) ,
  “ (safeExec ATrue (return (l4)) X_low_level_spec ) ”
  &&  (sll x l4 )
).

Definition glibc_slist_clean_multi_merge_return_wit_3 := 
(
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre = 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec )
|--
  EX (l4: (@list Z)) ,
  “ (safeExec ATrue (return (l4)) X_low_level_spec ) ”
  &&  (sll z_pre l4 )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre = 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (return (l3_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_multi_merge_return_wit_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre = 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (return (l3_low_level_spec)) X_low_level_spec ) ”
.

Definition glibc_slist_clean_multi_merge_return_wit_3_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (l3_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (y_pre = 0)) (PreH2 : (x_pre = 0)) (PreH3 : (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  TT && emp 
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (x_pre <> 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (y <> 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (ty <> 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (y_pre <> 0)) (PreH7 : (x_pre = 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (y <> 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_3 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z <> 0)) (PreH2 : (ty = 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z <> 0)) (PreH2 : (ty = 0)) (PreH3 : (z <> 0)) (PreH4 : (y = 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (y_pre <> 0)) (PreH8 : (x_pre = 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z <> 0)) (PreH2 : (ty = 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (y_pre <> 0)) (PreH7 : (x_pre = 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_6 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z <> 0)) (PreH2 : (ty = 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (x_pre <> 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z <> 0)) (PreH2 : (y = 0)) (PreH3 : (ty <> 0)) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH7 : (cursor <> 0)) (PreH8 : (y_pre <> 0)) (PreH9 : (x_pre = 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_8 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z <> 0)) (PreH2 : (y = 0)) (PreH3 : (ty <> 0)) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH7 : (cursor <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (x_pre <> 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (ty = 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (y_pre <> 0)) (PreH7 : (x_pre = 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (z = 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_10 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (PreH1 : (z = 0)) (PreH2 : (ty = 0)) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (x_pre <> 0)) ,
  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll z l4 )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (z = 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_11 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l3 = (cons (x_2) (l0)))) (PreH2 : (y <> 0)) (PreH3 : (ty <> 0)) (PreH4 : (y <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (y <> 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll z l4 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_12 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l3 = (cons (x_2) (l0)))) (PreH2 : (y <> 0)) (PreH3 : (ty <> 0)) (PreH4 : (y <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (y_pre <> 0)) (PreH8 : (x_pre = 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (y <> 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_13 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l4 = (cons (x_2) (l0)))) (PreH2 : (z <> 0)) (PreH3 : (ty = 0)) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH7 : (cursor <> 0)) (PreH8 : (x_pre <> 0)) (PreH9 : (x_pre <> 0)) ,
  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll y l3 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l4 = (cons (x_2) (l0)))) (PreH2 : (z <> 0)) (PreH3 : (ty = 0)) (PreH4 : (z <> 0)) (PreH5 : (y = 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH7 : (cursor <> 0)) (PreH8 : (y_pre <> 0)) (PreH9 : (x_pre = 0)) ,
  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_15 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l4 = (cons (x_2) (l0)))) (PreH2 : (z <> 0)) (PreH3 : (ty = 0)) (PreH4 : (y <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (y_pre <> 0)) (PreH8 : (x_pre = 0)) ,
  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_16 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l4 = (cons (x_2) (l0)))) (PreH2 : (z <> 0)) (PreH3 : (ty = 0)) (PreH4 : (y <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll y l3 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_17 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l4 = (cons (x_2) (l0)))) (PreH2 : (z <> 0)) (PreH3 : (y = 0)) (PreH4 : (ty <> 0)) (PreH5 : (z <> 0)) (PreH6 : (y = 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (y_pre <> 0)) (PreH10 : (x_pre = 0)) ,
  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll y l3 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_18 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l4 = (cons (x_2) (l0)))) (PreH2 : (z <> 0)) (PreH3 : (y = 0)) (PreH4 : (ty <> 0)) (PreH5 : (z <> 0)) (PreH6 : (y = 0)) (PreH7 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH8 : (cursor <> 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (x_pre <> 0)) ,
  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l4 = (cons (x_2) (l0))) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (ty <> 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y = 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll y l3 )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_19 := 
forall (y_pre: Z) (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l3 = (cons (x_2) (l0)))) (PreH2 : (z = 0)) (PreH3 : (ty = 0)) (PreH4 : (y <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (y_pre <> 0)) (PreH8 : (x_pre = 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (z = 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (y_pre <> 0) ” 
  &&  “ (x_pre = 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll z l4 )
  **  (sll x_pre l1_low_level_spec )
.

Definition glibc_slist_clean_multi_merge_partial_solve_wit_20 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (z: Z) (y: Z) (x: Z) (ty: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (l4: (@list Z)) (x_2: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l3 = (cons (x_2) (l0)))) (PreH2 : (z = 0)) (PreH3 : (ty = 0)) (PreH4 : (y <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll cursor l2 )
  **  (sll z l4 )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_3: Z) ,
  “ (l2 = (cons (x_3) (l0_2))) ” 
  &&  “ (l3 = (cons (x_2) (l0))) ” 
  &&  “ (z = 0) ” 
  &&  “ (ty = 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_multi_merge_M_loop (l1) (l2) (l3) (l4))) (glibc_slist_clean_multi_merge_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x cursor l1 )
  **  (sll z l4 )
.

Definition glibc_slist_clean_multi_merge_derive_high_level_spec_by_low_level_spec := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (l3_high_level_spec: (@list Z)) (l2_high_level_spec: (@list Z)) (l1_high_level_spec: (@list Z)) ,
  (sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec )
  **  (sll z_pre l3_high_level_spec )
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (l3_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (glibc_slist_clean_multi_merge_M (l1_low_level_spec) (l2_low_level_spec) (l3_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
  **  (sll z_pre l3_low_level_spec ))
  **
  ((EX l4_2 retval_2,
  “ (safeExec ATrue (return (l4_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l4_2 ))
  -*
  (EX l4 retval,
  “ (Permutation l4 (app ((app (l1_high_level_spec) (l2_high_level_spec))) (l3_high_level_spec)) ) ”
  &&  (sll retval l4 )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_1 : glibc_slist_clean_multi_merge_safety_wit_1.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_2 : glibc_slist_clean_multi_merge_safety_wit_2.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_3 : glibc_slist_clean_multi_merge_safety_wit_3.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_4 : glibc_slist_clean_multi_merge_safety_wit_4.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_5 : glibc_slist_clean_multi_merge_safety_wit_5.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_6 : glibc_slist_clean_multi_merge_safety_wit_6.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_7 : glibc_slist_clean_multi_merge_safety_wit_7.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_8 : glibc_slist_clean_multi_merge_safety_wit_8.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_9 : glibc_slist_clean_multi_merge_safety_wit_9.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_10 : glibc_slist_clean_multi_merge_safety_wit_10.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_11 : glibc_slist_clean_multi_merge_safety_wit_11.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_12 : glibc_slist_clean_multi_merge_safety_wit_12.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_13 : glibc_slist_clean_multi_merge_safety_wit_13.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_14 : glibc_slist_clean_multi_merge_safety_wit_14.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_15 : glibc_slist_clean_multi_merge_safety_wit_15.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_16 : glibc_slist_clean_multi_merge_safety_wit_16.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_17 : glibc_slist_clean_multi_merge_safety_wit_17.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_18 : glibc_slist_clean_multi_merge_safety_wit_18.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_19 : glibc_slist_clean_multi_merge_safety_wit_19.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_20 : glibc_slist_clean_multi_merge_safety_wit_20.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_21 : glibc_slist_clean_multi_merge_safety_wit_21.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_22 : glibc_slist_clean_multi_merge_safety_wit_22.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_23 : glibc_slist_clean_multi_merge_safety_wit_23.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_24 : glibc_slist_clean_multi_merge_safety_wit_24.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_25 : glibc_slist_clean_multi_merge_safety_wit_25.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_26 : glibc_slist_clean_multi_merge_safety_wit_26.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_27 : glibc_slist_clean_multi_merge_safety_wit_27.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_28 : glibc_slist_clean_multi_merge_safety_wit_28.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_29 : glibc_slist_clean_multi_merge_safety_wit_29.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_30 : glibc_slist_clean_multi_merge_safety_wit_30.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_31 : glibc_slist_clean_multi_merge_safety_wit_31.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_32 : glibc_slist_clean_multi_merge_safety_wit_32.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_33 : glibc_slist_clean_multi_merge_safety_wit_33.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_34 : glibc_slist_clean_multi_merge_safety_wit_34.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_35 : glibc_slist_clean_multi_merge_safety_wit_35.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_36 : glibc_slist_clean_multi_merge_safety_wit_36.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_37 : glibc_slist_clean_multi_merge_safety_wit_37.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_38 : glibc_slist_clean_multi_merge_safety_wit_38.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_39 : glibc_slist_clean_multi_merge_safety_wit_39.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_40 : glibc_slist_clean_multi_merge_safety_wit_40.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_41 : glibc_slist_clean_multi_merge_safety_wit_41.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_42 : glibc_slist_clean_multi_merge_safety_wit_42.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_43 : glibc_slist_clean_multi_merge_safety_wit_43.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_44 : glibc_slist_clean_multi_merge_safety_wit_44.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_45 : glibc_slist_clean_multi_merge_safety_wit_45.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_46 : glibc_slist_clean_multi_merge_safety_wit_46.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_47 : glibc_slist_clean_multi_merge_safety_wit_47.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_48 : glibc_slist_clean_multi_merge_safety_wit_48.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_49 : glibc_slist_clean_multi_merge_safety_wit_49.
Axiom proof_of_glibc_slist_clean_multi_merge_safety_wit_50 : glibc_slist_clean_multi_merge_safety_wit_50.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_1_1 : glibc_slist_clean_multi_merge_entail_wit_1_1.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_1_2 : glibc_slist_clean_multi_merge_entail_wit_1_2.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_1 : glibc_slist_clean_multi_merge_entail_wit_2_1.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_2 : glibc_slist_clean_multi_merge_entail_wit_2_2.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_3 : glibc_slist_clean_multi_merge_entail_wit_2_3.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_4 : glibc_slist_clean_multi_merge_entail_wit_2_4.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_5 : glibc_slist_clean_multi_merge_entail_wit_2_5.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_6 : glibc_slist_clean_multi_merge_entail_wit_2_6.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_7 : glibc_slist_clean_multi_merge_entail_wit_2_7.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_8 : glibc_slist_clean_multi_merge_entail_wit_2_8.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_9 : glibc_slist_clean_multi_merge_entail_wit_2_9.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_10 : glibc_slist_clean_multi_merge_entail_wit_2_10.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_11 : glibc_slist_clean_multi_merge_entail_wit_2_11.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_12 : glibc_slist_clean_multi_merge_entail_wit_2_12.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_13 : glibc_slist_clean_multi_merge_entail_wit_2_13.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_14 : glibc_slist_clean_multi_merge_entail_wit_2_14.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_15 : glibc_slist_clean_multi_merge_entail_wit_2_15.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_16 : glibc_slist_clean_multi_merge_entail_wit_2_16.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_17 : glibc_slist_clean_multi_merge_entail_wit_2_17.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_18 : glibc_slist_clean_multi_merge_entail_wit_2_18.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_19 : glibc_slist_clean_multi_merge_entail_wit_2_19.
Axiom proof_of_glibc_slist_clean_multi_merge_entail_wit_2_20 : glibc_slist_clean_multi_merge_entail_wit_2_20.
Axiom proof_of_glibc_slist_clean_multi_merge_return_wit_1 : glibc_slist_clean_multi_merge_return_wit_1.
Axiom proof_of_glibc_slist_clean_multi_merge_return_wit_2 : glibc_slist_clean_multi_merge_return_wit_2.
Axiom proof_of_glibc_slist_clean_multi_merge_return_wit_3 : glibc_slist_clean_multi_merge_return_wit_3.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_1 : glibc_slist_clean_multi_merge_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_2 : glibc_slist_clean_multi_merge_partial_solve_wit_2.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_3 : glibc_slist_clean_multi_merge_partial_solve_wit_3.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_4 : glibc_slist_clean_multi_merge_partial_solve_wit_4.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_5 : glibc_slist_clean_multi_merge_partial_solve_wit_5.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_6 : glibc_slist_clean_multi_merge_partial_solve_wit_6.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_7 : glibc_slist_clean_multi_merge_partial_solve_wit_7.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_8 : glibc_slist_clean_multi_merge_partial_solve_wit_8.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_9 : glibc_slist_clean_multi_merge_partial_solve_wit_9.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_10 : glibc_slist_clean_multi_merge_partial_solve_wit_10.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_11 : glibc_slist_clean_multi_merge_partial_solve_wit_11.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_12 : glibc_slist_clean_multi_merge_partial_solve_wit_12.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_13 : glibc_slist_clean_multi_merge_partial_solve_wit_13.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_14 : glibc_slist_clean_multi_merge_partial_solve_wit_14.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_15 : glibc_slist_clean_multi_merge_partial_solve_wit_15.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_16 : glibc_slist_clean_multi_merge_partial_solve_wit_16.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_17 : glibc_slist_clean_multi_merge_partial_solve_wit_17.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_18 : glibc_slist_clean_multi_merge_partial_solve_wit_18.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_19 : glibc_slist_clean_multi_merge_partial_solve_wit_19.
Axiom proof_of_glibc_slist_clean_multi_merge_partial_solve_wit_20 : glibc_slist_clean_multi_merge_partial_solve_wit_20.
Axiom proof_of_glibc_slist_clean_multi_merge_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_multi_merge_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
