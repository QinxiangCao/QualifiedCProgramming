From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_goal.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_proof.

(*----- Function LOS_ListDelete -----*)

Definition LOS_ListDelete_safety_wit_1 :=
forall (A: Type) (next_low_level_spec: Z) (prev_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition LOS_ListDelete_safety_wit_2 :=
forall (A: Type) (next_low_level_spec: Z) (prev_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> 0)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition LOS_ListDelete_return_wit_1 :=
(
forall (A: Type) (next_low_level_spec: Z) (prev_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> 0)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> 0)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
) \/
(
forall (A: Type) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
|--
  TT && emp 
).

Definition LOS_ListDelete_return_wit_1_split_goal_spatial :=
forall (A: Type) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
|--
  TT && emp 
.

Definition LOS_ListDelete_partial_solve_wit_1 :=
forall (A: Type) (next_low_level_spec: Z) (prev_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  (dllseg_shift storeA_low_level_spec prev_low_level_spec node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) ((@nil (@DL_Node A)))) )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
.

Definition LOS_ListDelete_partial_solve_wit_2 :=
forall (A: Type) (next_low_level_spec: Z) (prev_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  (dllseg_shift storeA_low_level_spec prev_low_level_spec node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) ((@nil (@DL_Node A)))) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
.

Definition LOS_ListDelete_partial_solve_wit_3 :=
forall (A: Type) (next_low_level_spec: Z) (prev_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (node_pre: Z),
  (dllseg_shift storeA_low_level_spec prev_low_level_spec node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) ((@nil (@DL_Node A)))) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
|--
  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  (dllseg_shift storeA_low_level_spec node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec)
.

(* Shallow FunAssertion specs for LOS_ListDelete. *)
Definition LOS_ListDelete_sig : FuncSig := ([ * struct "LOS_DL_LIST"], void)%ctype.

Definition LOS_ListDelete_low_level_spec : Spec LOS_ListDelete_sig :=
  fun F =>
ALL A : Type,
ALL (storeA: (Z -> (A -> Assertion))),
ALL (a: A),
ALL (prev: Z),
ALL (next: Z),
HoareFun ([ * struct "LOS_DL_LIST"], void)%ctype
  (fun node_pre =>
  (((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  (dllseg_shift storeA prev node_pre (cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))) )))
  (fun node_pre (_retval : unit) =>
  (((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA node_pre a )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)))
  F.

Definition LOS_ListDelete_mid_level_spec : Spec LOS_ListDelete_sig :=
  fun F =>
ALL A : Type,
ALL (storeA1: (Z -> (A -> Assertion))),
ALL (p: Z),
ALL (a: A),
ALL (l1: (@list (@DL_Node A))),
ALL (l2: (@list (@DL_Node A))),
HoareFun ([ * struct "LOS_DL_LIST"], void)%ctype
  (fun node_pre =>
  ((store_dll storeA1 p (app (l1) ((cons ((Build_DL_Node (a) (node_pre))) (l2)))) )))
  (fun node_pre (_retval : unit) =>
  ((store_dll storeA1 p (app (l1) (l2)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA1 node_pre a )))
  F.

Definition LOS_ListDelete_low_level_spec_entail_mid_level_spec :=
forall (A: Type),
forall (node_pre: Z) (storeA1_mid_level_spec: (Z -> (A -> Assertion))) (p_mid_level_spec: Z) (a_mid_level_spec: A) (l1_mid_level_spec: (@list (@DL_Node A))) (l2_mid_level_spec: (@list (@DL_Node A))),
  ((store_dll storeA1_mid_level_spec p_mid_level_spec (app (l1_mid_level_spec) ((cons ((Build_DL_Node (a_mid_level_spec) (node_pre))) (l2_mid_level_spec)))) ))
|--
EX (A_2: Type) ,
EX (storeA_low_level_spec: (Z -> (A_2 -> Assertion)))(a_low_level_spec: A_2)(prev_low_level_spec: Z)(next_low_level_spec: Z),
  (((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  (dllseg_shift storeA_low_level_spec prev_low_level_spec node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) (nil)) ))
  **
  (  (((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((prev_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev_low_level_spec))
  -*
  ((store_dll storeA1_mid_level_spec p_mid_level_spec (app (l1_mid_level_spec) (l2_mid_level_spec)) )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  (storeA1_mid_level_spec node_pre a_mid_level_spec )))
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListDelete_safety_wit_1 : LOS_ListDelete_safety_wit_1.
Axiom proof_of_LOS_ListDelete_safety_wit_2 : LOS_ListDelete_safety_wit_2.
Axiom proof_of_LOS_ListDelete_return_wit_1 : LOS_ListDelete_return_wit_1.
Axiom proof_of_LOS_ListDelete_partial_solve_wit_1 : LOS_ListDelete_partial_solve_wit_1.
Axiom proof_of_LOS_ListDelete_partial_solve_wit_2 : LOS_ListDelete_partial_solve_wit_2.
Axiom proof_of_LOS_ListDelete_partial_solve_wit_3 : LOS_ListDelete_partial_solve_wit_3.
Axiom proof_of_LOS_ListDelete_low_level_spec_entail_mid_level_spec : LOS_ListDelete_low_level_spec_entail_mid_level_spec.

End VC_Correct.
