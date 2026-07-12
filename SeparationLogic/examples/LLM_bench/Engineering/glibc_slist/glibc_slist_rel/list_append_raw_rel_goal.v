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
Require Import list_append_raw_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function list_append_raw -----*)

Definition list_append_raw_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  ((( &( "tail" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition list_append_raw_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
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
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  emp
).

Definition list_append_raw_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )
.

Definition list_append_raw_entail_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2: (@list Z)) (v_2: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (v_2))))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (retval <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (x_pre <> 0)) ,
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (sllseg x_pre retval l2 )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l3: (@list Z))  (v: Z) ,
  “ (safeExec ATrue (bind ((return ((maketuple (l3) (v))))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg x_pre retval l3 )
  **  (sll y_pre l2_low_level_spec )
.

Definition list_append_raw_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (retval: Z) (l3_2: (@list Z)) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l3_2) (v))))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (retval <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (x_pre <> 0)) ,
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg x_pre retval l3_2 )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll x_pre l3 )
) \/
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (retval: Z) (l3_2: (@list Z)) (v: Z) (PreH1 : (v <= INT_MAX)) (PreH2 : (v >= INT_MIN)) (PreH3 : (safeExec ATrue (bind ((return ((maketuple (l3_2) (v))))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH4 : (retval <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (x_pre <> 0)) ,
  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg x_pre retval l3_2 )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ (safeExec ATrue (return ((cons (x) (l0)))) X_low_level_spec ) ”
  &&  (sll y l0 )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
).

Definition list_append_raw_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll y_pre l3 )
) \/
(
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return (l2_low_level_spec)) X_low_level_spec ) ”
  &&  emp
).

Definition list_append_raw_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return (l2_low_level_spec)) X_low_level_spec ) ”
.

Definition list_append_raw_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  TT && emp 
.

Definition list_append_raw_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (x_pre <> 0)) ,
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
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (bind ((list_tail_M (l1_low_level_spec))) ((residual_prog_in_list_append_raw_M_call_1 (l2_low_level_spec)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (x_pre <> 0)) ,
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

Definition list_append_raw_derive_high_level_spec_by_low_level_spec := 
forall (y_pre: Z) (x_pre: Z) (l2_high_level_spec: (@list Z)) (l1_high_level_spec: (@list Z)) ,
  (sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec )
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (list_append_raw_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
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

Axiom proof_of_list_append_raw_safety_wit_1 : list_append_raw_safety_wit_1.
Axiom proof_of_list_append_raw_entail_wit_1 : list_append_raw_entail_wit_1.
Axiom proof_of_list_append_raw_entail_wit_2 : list_append_raw_entail_wit_2.
Axiom proof_of_list_append_raw_return_wit_1 : list_append_raw_return_wit_1.
Axiom proof_of_list_append_raw_return_wit_2 : list_append_raw_return_wit_2.
Axiom proof_of_list_append_raw_partial_solve_wit_1_pure : list_append_raw_partial_solve_wit_1_pure.
Axiom proof_of_list_append_raw_partial_solve_wit_1 : list_append_raw_partial_solve_wit_1.
Axiom proof_of_list_append_raw_derive_high_level_spec_by_low_level_spec : list_append_raw_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
