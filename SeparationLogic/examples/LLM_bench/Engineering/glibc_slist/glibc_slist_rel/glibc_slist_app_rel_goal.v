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
Require Import glibc_slist_app_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_app -----*)

Definition glibc_slist_clean_app_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
) \/
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_app_entail_wit_1_split_goal_1 := 
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )
.

Definition glibc_slist_clean_app_return_wit_1 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )) ,
  (sll retval l3_2 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll retval l3 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (return (l3_2)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_app_return_wit_1_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )) ,
  (safeExec ATrue (return (l3_2)) X_low_level_spec )
.

Definition glibc_slist_clean_app_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
.

Definition glibc_slist_clean_app_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
.

Definition glibc_slist_clean_app_partial_solve_wit_1 := glibc_slist_clean_app_partial_solve_wit_1_pure -> glibc_slist_clean_app_partial_solve_wit_1_aux.

Definition glibc_slist_clean_app_derive_high_level_spec_by_low_level_spec := 
forall (y_pre: Z) (x_pre: Z) (l2_high_level_spec: (@list Z)) (l1_high_level_spec: (@list Z)) ,
  (sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec )
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec ))
  **
  ((EX l3 retval_2,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll retval_2 l3 ))
  -*
  (EX retval,
  (sll retval (app (l1_high_level_spec) (l2_high_level_spec)) )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_app_entail_wit_1 : glibc_slist_clean_app_entail_wit_1.
Axiom proof_of_glibc_slist_clean_app_return_wit_1 : glibc_slist_clean_app_return_wit_1.
Axiom proof_of_glibc_slist_clean_app_partial_solve_wit_1_pure : glibc_slist_clean_app_partial_solve_wit_1_pure.
Axiom proof_of_glibc_slist_clean_app_partial_solve_wit_1 : glibc_slist_clean_app_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_app_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_app_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
