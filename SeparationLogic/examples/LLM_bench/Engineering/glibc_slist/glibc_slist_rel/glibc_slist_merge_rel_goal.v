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
Require Import glibc_slist_merge_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_merge -----*)

Definition glibc_slist_clean_merge_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "cursor" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_merge_safety_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH2 : (cursor <> 0)) (PreH3 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "cursor" ) )) # Ptr  |-> cursor)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sllseg head cursor l1 )
  **  (sll cursor l2 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_merge_safety_wit_3 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (y_2: Z) (x_2: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (l2 = (cons (x_2) (l0_2)))) (PreH2 : (l3 = (cons (x) (l0)))) (PreH3 : (y <> 0)) (PreH4 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH5 : (cursor <> 0)) (PreH6 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "cursor" ) )) # Ptr  |-> y)
  **  ((( &( "node" ) )) # Ptr  |-> y)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  (sllseg head cursor l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_merge_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x_pre x_pre l1 )
  **  (sll x_pre l2 )
  **  (sll y_pre l3 )
) \/
(
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop ((@nil Z)) (l1_low_level_spec) (l2_low_level_spec))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_merge_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop ((@nil Z)) (l1_low_level_spec) (l2_low_level_spec))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )
.

Definition glibc_slist_clean_merge_entail_wit_2 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y_3: Z) (head: Z) (cursor: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (x_2: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (y_2 <> 0)) (PreH2 : (l2_2 = (cons (x_2) (l0_2)))) (PreH3 : (l3_2 = (cons (x) (l0)))) (PreH4 : (y_3 <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1_2) (l2_2) (l3_2))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_2 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y l0 )
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "node" ) )) # Ptr  |-> y_3)
  **  (sllseg head cursor l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sllseg head y_2 l1 )
  **  (sll y_2 l2 )
  **  (sll y l3 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y_3: Z) (head: Z) (cursor: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x: Z) (l0: (@list Z)) (x_2: Z) (l0_2: (@list Z)) (y_2: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (x_2 <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (x_2 >= INT_MIN)) (PreH5 : (y_2 <> 0)) (PreH6 : (l2_2 = (cons (x_2) (l0_2)))) (PreH7 : (l3_2 = (cons (x) (l0)))) (PreH8 : (y_3 <> 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1_2) (l2_2) (l3_2))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllseg head cursor l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l0_2) (l0))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec ) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg head y_2 l1 )
).

Definition glibc_slist_clean_merge_return_wit_1 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3_2))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH3 : (cursor <> 0)) (PreH4 : (x_pre <> 0)) ,
  (sllseg head cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3_2 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll head l3 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3_2))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH3 : (cursor <> 0)) (PreH4 : (x_pre <> 0)) ,
  (sllseg head cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3_2 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll head l3 )
).

Definition glibc_slist_clean_merge_return_wit_2 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3_2: (@list Z)) (x: Z) (l0: (@list Z)) (y_2: Z) (x_2: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (l2 = (cons (x_2) (l0_2)))) (PreH3 : (l3_2 = (cons (x) (l0)))) (PreH4 : (y <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3_2))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH6 : (cursor <> 0)) (PreH7 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllseg head cursor l1 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll head l3 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3_2: (@list Z)) (x: Z) (l0: (@list Z)) (y_2: Z) (x_2: Z) (l0_2: (@list Z)) (y_3: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (x_2 <= INT_MAX)) (PreH3 : (x >= INT_MIN)) (PreH4 : (x_2 >= INT_MIN)) (PreH5 : (y_3 = 0)) (PreH6 : (l2 = (cons (x_2) (l0_2)))) (PreH7 : (l3_2 = (cons (x) (l0)))) (PreH8 : (y <> 0)) (PreH9 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3_2))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH10 : (cursor <> 0)) (PreH11 : (x_pre <> 0)) ,
  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllseg head cursor l1 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll head l3 )
).

Definition glibc_slist_clean_merge_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll y_pre l3 )
) \/
(
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return (l2_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_merge_return_wit_3_split_goal_1 := 
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return (l2_low_level_spec)) X_low_level_spec ) ”
.

Definition glibc_slist_clean_merge_return_wit_3_split_goal_spatial := 
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  TT && emp 
.

Definition glibc_slist_clean_merge_partial_solve_wit_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH3 : (cursor <> 0)) (PreH4 : (x_pre <> 0)) ,
  (sllseg head cursor l1 )
  **  (sll cursor l2 )
  **  (sll y l3 )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x: Z) ,
  “ (l3 = (cons (x) (l0))) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllseg head cursor l1 )
  **  (sll cursor l2 )
.

Definition glibc_slist_clean_merge_partial_solve_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (head: Z) (cursor: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (y_2: Z) (PreH1 : (l3 = (cons (x) (l0)))) (PreH2 : (y <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec )) (PreH4 : (cursor <> 0)) (PreH5 : (x_pre <> 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllseg head cursor l1 )
  **  (sll cursor l2 )
|--
  EX (y_3: Z)  (l0_2: (@list Z))  (x_2: Z) ,
  “ (l2 = (cons (x_2) (l0_2))) ” 
  &&  “ (l3 = (cons (x) (l0))) ” 
  &&  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_merge_M_loop (l1) (l2) (l3))) (glibc_slist_clean_merge_M_after_loop)) X_low_level_spec ) ” 
  &&  “ (cursor <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((cursor)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (sll y_3 l0_2 )
  **  ((&((cursor)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sllseg head cursor l1 )
.

Definition glibc_slist_clean_merge_derive_high_level_spec_by_low_level_spec := 
forall (y_pre: Z) (x_pre: Z) (l2_high_level_spec: (@list Z)) (l1_high_level_spec: (@list Z)) ,
  (sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec )
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (glibc_slist_clean_merge_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec ))
  **
  ((EX l3_2 retval_2,
  “ (safeExec ATrue (return (l3_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l3_2 ))
  -*
  (EX l3 retval,
  “ (Permutation l3 (app (l1_high_level_spec) (l2_high_level_spec)) ) ”
  &&  (sll retval l3 )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_merge_safety_wit_1 : glibc_slist_clean_merge_safety_wit_1.
Axiom proof_of_glibc_slist_clean_merge_safety_wit_2 : glibc_slist_clean_merge_safety_wit_2.
Axiom proof_of_glibc_slist_clean_merge_safety_wit_3 : glibc_slist_clean_merge_safety_wit_3.
Axiom proof_of_glibc_slist_clean_merge_entail_wit_1 : glibc_slist_clean_merge_entail_wit_1.
Axiom proof_of_glibc_slist_clean_merge_entail_wit_2 : glibc_slist_clean_merge_entail_wit_2.
Axiom proof_of_glibc_slist_clean_merge_return_wit_1 : glibc_slist_clean_merge_return_wit_1.
Axiom proof_of_glibc_slist_clean_merge_return_wit_2 : glibc_slist_clean_merge_return_wit_2.
Axiom proof_of_glibc_slist_clean_merge_return_wit_3 : glibc_slist_clean_merge_return_wit_3.
Axiom proof_of_glibc_slist_clean_merge_partial_solve_wit_1 : glibc_slist_clean_merge_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_merge_partial_solve_wit_2 : glibc_slist_clean_merge_partial_solve_wit_2.
Axiom proof_of_glibc_slist_clean_merge_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_merge_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
