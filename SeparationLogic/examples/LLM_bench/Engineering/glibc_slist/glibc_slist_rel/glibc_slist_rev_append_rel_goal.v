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
Require Import glibc_slist_rev_append_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_rev_append -----*)

Definition glibc_slist_clean_rev_append_safety_wit_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_rev_append_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_rev_append_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec ) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
) \/
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_rev_append_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1_low_level_spec) (l2_low_level_spec))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_rev_append_entail_wit_1_split_goal_1 := 
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_rev_append_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1_low_level_spec) (l2_low_level_spec))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )
.

Definition glibc_slist_clean_rev_append_entail_wit_2 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y_2: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l1_2 = (cons (x_2) (l0)))) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1_2) (l2_2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y l0 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "t" ) )) # Ptr  |-> y)
  **  (sll y_2 l2_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec ) ”
  &&  ((( &( "t" ) )) # Ptr  |->_)
  **  (sll y l1 )
  **  (sll x l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_2: Z) (l0: (@list Z)) (PreH1 : (l1_2 = (cons (x_2) (l0)))) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1_2) (l2_2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l0) ((cons (x_2) (l2_2))))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_rev_append_entail_wit_2_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_2: Z) (l0: (@list Z)) (PreH1 : (l1_2 = (cons (x_2) (l0)))) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1_2) (l2_2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l0) ((cons (x_2) (l2_2))))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )
.

Definition glibc_slist_clean_rev_append_return_wit_1 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  (sll x l1 )
  **  (sll y l2 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll y l3 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  (sll x l1 )
|--
  “ (safeExec ATrue (return (l2)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_rev_append_return_wit_1_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  (sll x l1 )
|--
  “ (safeExec ATrue (return (l2)) X_low_level_spec ) ”
.

Definition glibc_slist_clean_rev_append_return_wit_1_split_goal_spatial := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  (sll x l1 )
|--
  TT && emp 
.

Definition glibc_slist_clean_rev_append_partial_solve_wit_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x <> 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec )) ,
  (sll x l1 )
  **  (sll y l2 )
|--
  EX (y_2: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l1 = (cons (x_2) (l0))) ” 
  &&  “ (x <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_rev_append_M_loop (l1) (l2))) (glibc_slist_clean_rev_append_M_loop_end)) X_low_level_spec ) ”
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (sll y_2 l0 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sll y l2 )
.

Definition glibc_slist_clean_rev_append_derive_high_level_spec_by_low_level_spec := 
forall (y_pre: Z) (x_pre: Z) (l2_high_level_spec: (@list Z)) (l1_high_level_spec: (@list Z)) ,
  (sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec )
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (glibc_slist_clean_rev_append_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec ))
  **
  ((EX l3 retval_2,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll retval_2 l3 ))
  -*
  (EX retval,
  (sll retval (app ((rev (l1_high_level_spec))) (l2_high_level_spec)) )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_rev_append_safety_wit_1 : glibc_slist_clean_rev_append_safety_wit_1.
Axiom proof_of_glibc_slist_clean_rev_append_entail_wit_1 : glibc_slist_clean_rev_append_entail_wit_1.
Axiom proof_of_glibc_slist_clean_rev_append_entail_wit_2 : glibc_slist_clean_rev_append_entail_wit_2.
Axiom proof_of_glibc_slist_clean_rev_append_return_wit_1 : glibc_slist_clean_rev_append_return_wit_1.
Axiom proof_of_glibc_slist_clean_rev_append_partial_solve_wit_1 : glibc_slist_clean_rev_append_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_rev_append_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_rev_append_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
