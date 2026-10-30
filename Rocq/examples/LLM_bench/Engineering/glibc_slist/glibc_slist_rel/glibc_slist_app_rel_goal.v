From SimpleC.Verification Require Import VCPrelude.
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
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
) \/
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_app_entail_wit_1_split_goal_1 :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )
.

Definition glibc_slist_clean_app_return_wit_1 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )),
  (sll retval l3_2 )
|--
  EX (l3: (@list Z)),
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll retval l3 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (return (l3_2)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_app_return_wit_1_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )),
  (safeExec ATrue (return (l3_2)) X_low_level_spec )
.

Definition glibc_slist_clean_app_partial_solve_wit_1_pure :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
.

Definition glibc_slist_clean_app_partial_solve_wit_1_aux :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((list_append_raw_M (l1_low_level_spec) (l2_low_level_spec))) (residual_prog_in_glibc_slist_clean_app_M_call_1)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
.

Definition glibc_slist_clean_app_partial_solve_wit_1 := glibc_slist_clean_app_partial_solve_wit_1_pure -> glibc_slist_clean_app_partial_solve_wit_1_aux.

(* Shallow FunAssertion specs for glibc_slist_clean_app. *)
Definition glibc_slist_clean_app_sig : FuncSig := ([ * struct "list";  * struct "list"],  * struct "list")%ctype.

Definition glibc_slist_clean_app_low_level_spec : Spec glibc_slist_clean_app_sig :=
  fun F =>
ALL (X: ((@list Z) -> (unit -> Prop))),
ALL (l1: (@list Z)),
ALL (l2: (@list Z)),
HoareFun ([ * struct "list";  * struct "list"],  * struct "list")%ctype
  (fun '(x_pre, y_pre) =>
  (“ (safeExec ATrue (glibc_slist_clean_app_M (l1) (l2)) X ) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )))
  (fun '(x_pre, y_pre) retval =>
  (EX (l3: (@list Z)),
  “ (safeExec ATrue (return (l3)) X ) ”
  &&  (sll retval l3 )))
  F.

Definition glibc_slist_clean_app_high_level_spec : Spec glibc_slist_clean_app_sig :=
  fun F =>
ALL (l1: (@list Z)),
ALL (l2: (@list Z)),
HoareFun ([ * struct "list";  * struct "list"],  * struct "list")%ctype
  (fun '(x_pre, y_pre) =>
  ((sll x_pre l1 )
  **  (sll y_pre l2 )))
  (fun '(x_pre, y_pre) retval =>
  ((sll retval (app (l1) (l2)) )))
  F.

Definition glibc_slist_clean_app_low_level_spec_entail_high_level_spec :=
forall (x_pre: Z) (y_pre: Z) (l1_high_level_spec: (@list Z)) (l2_high_level_spec: (@list Z)),
  ((sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec ))
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop)))(l1_low_level_spec: (@list Z))(l2_low_level_spec: (@list Z)),
  (“ (safeExec ATrue (glibc_slist_clean_app_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l3: (@list Z)),
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll retval l3 ))
  -*
  ((sll retval (app (l1_high_level_spec) (l2_high_level_spec)) )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_app_entail_wit_1 : glibc_slist_clean_app_entail_wit_1.
Axiom proof_of_glibc_slist_clean_app_return_wit_1 : glibc_slist_clean_app_return_wit_1.
Axiom proof_of_glibc_slist_clean_app_partial_solve_wit_1_pure : glibc_slist_clean_app_partial_solve_wit_1_pure.
Axiom proof_of_glibc_slist_clean_app_partial_solve_wit_1 : glibc_slist_clean_app_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_app_low_level_spec_entail_high_level_spec : glibc_slist_clean_app_low_level_spec_entail_high_level_spec.

End VC_Correct.
