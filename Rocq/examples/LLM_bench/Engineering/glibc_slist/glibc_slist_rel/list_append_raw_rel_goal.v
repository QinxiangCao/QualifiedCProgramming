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
Require Import list_append_raw_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function list_append_raw -----*)

Definition list_append_raw_safety_wit_1 :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  ((( &( "tail" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition list_append_raw_entail_wit_1 :=
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  “ (x_pre <> 0) ”
  &&  “ (x_pre <> 0) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
) \/
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  emp
).

Definition list_append_raw_entail_wit_1_split_goal_1 :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )
.

Definition list_append_raw_return_wit_1 :=
(
forall (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (l2: (@list Z)) (v: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (v))))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (retval <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (x_pre <> 0)),
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg x_pre retval l2 )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l3: (@list Z)),
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll x_pre l3 )
) \/
(
forall (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (l2: (@list Z)) (v: Z) (retval: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (v >= INT_MIN)) (PreH3 : (safeExec ATrue (bind ((return ((maketuple (l2) (v))))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH4 : (retval <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)),
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg x_pre retval l2 )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (y: Z) (l0: (@list Z)) (x: Z),
  “ (x_pre <> 0) ”
  &&  “ (safeExec ATrue (return ((cons (x) (l0)))) X_low_level_spec ) ”
  &&  (sll y l0 )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
).

Definition list_append_raw_return_wit_2 :=
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l3: (@list Z)),
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll y_pre l3 )
) \/
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return (l2_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition list_append_raw_return_wit_2_split_goal_1 :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return (l2_low_level_spec)) X_low_level_spec ) ”
.

Definition list_append_raw_return_wit_2_split_goal_spatial :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  TT && emp 
.

Definition list_append_raw_partial_solve_wit_1_pure :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (x_pre <> 0)),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll y_pre l2_low_level_spec )
  **  ((( &( "tail" ) )) # Ptr  |->_)
|--
  “ (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  “ (x_pre <> 0) ”
.

Definition list_append_raw_partial_solve_wit_1_aux :=
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (y_pre: Z) (PreH1 : (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (x_pre <> 0)),
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  “ (x_pre <> 0) ”
  &&  “ (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  “ (x_pre <> 0) ”
  &&  “ (x_pre <> 0) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
.

Definition list_append_raw_partial_solve_wit_1 := list_append_raw_partial_solve_wit_1_pure -> list_append_raw_partial_solve_wit_1_aux.

(* Shallow FunAssertion specs for list_append_raw. *)
Definition list_append_raw_sig : FuncSig := ([ * struct "list";  * struct "list"],  * struct "list")%ctype.

Definition list_append_raw_low_level_spec : Spec list_append_raw_sig :=
  fun F =>
ALL (X: ((@list Z) -> (unit -> Prop))),
ALL (l1: (@list Z)),
ALL (l2: (@list Z)),
HoareFun ([ * struct "list";  * struct "list"],  * struct "list")%ctype
  (fun '(x_pre, y_pre) =>
  (“ (safeExec ATrue (list_append_raw_M (l1) (l2)) X ) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )))
  (fun '(x_pre, y_pre) retval =>
  (EX (l3: (@list Z)),
  “ (safeExec ATrue (return (l3)) X ) ”
  &&  (sll retval l3 )))
  F.

Definition list_append_raw_high_level_spec : Spec list_append_raw_sig :=
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

Definition list_append_raw_low_level_spec_aux : Spec list_append_raw_sig :=
  fun F =>
ALL B : Type,
ALL (cont: ((@list Z) -> (@ MonadErr.M  unit B))),
ALL (X: (B -> (unit -> Prop))),
ALL (l1: (@list Z)),
ALL (l2: (@list Z)),
HoareFun ([ * struct "list";  * struct "list"],  * struct "list")%ctype
  (fun '(x_pre, y_pre) =>
  (“ (safeExec ATrue (bind ((list_append_raw_M (l1) (l2))) (cont)) X ) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )))
  (fun '(x_pre, y_pre) retval =>
  (EX (l3: (@list Z)),
  “ (safeExec ATrue (bind ((return (l3))) (cont)) X ) ”
  &&  (sll retval l3 )))
  F.

Definition list_append_raw_low_level_spec_entail_high_level_spec :=
forall (x_pre: Z) (y_pre: Z) (l1_high_level_spec: (@list Z)) (l2_high_level_spec: (@list Z)),
  ((sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec ))
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop)))(l1_low_level_spec: (@list Z))(l2_low_level_spec: (@list Z)),
  (“ (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
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

Axiom proof_of_list_append_raw_safety_wit_1 : list_append_raw_safety_wit_1.
Axiom proof_of_list_append_raw_entail_wit_1 : list_append_raw_entail_wit_1.
Axiom proof_of_list_append_raw_return_wit_1 : list_append_raw_return_wit_1.
Axiom proof_of_list_append_raw_return_wit_2 : list_append_raw_return_wit_2.
Axiom proof_of_list_append_raw_partial_solve_wit_1_pure : list_append_raw_partial_solve_wit_1_pure.
Axiom proof_of_list_append_raw_partial_solve_wit_1 : list_append_raw_partial_solve_wit_1.
Axiom proof_of_list_append_raw_low_level_spec_entail_high_level_spec : list_append_raw_low_level_spec_entail_high_level_spec.

End VC_Correct.
