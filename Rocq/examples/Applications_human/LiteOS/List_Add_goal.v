From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_goal.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_proof.

(*----- Function LOS_ListAdd -----*)

Definition LOS_ListAdd_return_wit_1 :=
(
forall (A: Type) (list_pstNext_low_level_spec: Z) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (list_pre: Z) (node_pre: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  ((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
|--
  ((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec list_pre node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) ((@nil (@DL_Node A)))) )
) \/
(
forall (A: Type) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (list_pre: Z) (node_pre: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
|--
  (dllseg_shift storeA_low_level_spec list_pre node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) ((@nil (@DL_Node A)))) )
).

Definition LOS_ListAdd_return_wit_1_split_goal_spatial :=
forall (A: Type) (a_low_level_spec: A) (storeA_low_level_spec: (Z -> (A -> Assertion))) (list_pre: Z) (node_pre: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
|--
  (dllseg_shift storeA_low_level_spec list_pre node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) ((@nil (@DL_Node A)))) )
.

(*----- Function LOS_ListTailInsert -----*)

Definition LOS_ListTailInsert_return_wit_1 :=
(
forall (A: Type) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (list_pre: Z) (node_pre: Z) (list_pstPrev: Z),
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  (dllseg_shift storeA list_pstPrev node_pre (cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))) )
  **  (dllseg_shift storeA list_pre list_pstPrev l )
|--
  (store_dll storeA list_pre (app (l) ((cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))))) )
) \/
(
forall (A: Type) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (list_pre: Z) (node_pre: Z) (list_pstPrev: Z),
  (dllseg_shift storeA node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (storeA node_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  (dllseg_shift storeA list_pre list_pstPrev l )
|--
  (store_dll storeA list_pre (app (l) ((cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))))) )
).

Definition LOS_ListTailInsert_return_wit_1_split_goal_spatial :=
forall (A: Type) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (list_pre: Z) (node_pre: Z) (list_pstPrev: Z),
  (dllseg_shift storeA node_pre node_pre (@nil (@DL_Node A)) )
  **  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (storeA node_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  (dllseg_shift storeA list_pre list_pstPrev l )
|--
  (store_dll storeA list_pre (app (l) ((cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))))) )
.

Definition LOS_ListTailInsert_partial_solve_wit_1 :=
forall (A: Type) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (pu: Z) (un: Z) (list_pre: Z) (node_pre: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
|--
  (store_dll storeA list_pre l )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
.

Definition LOS_ListTailInsert_partial_solve_wit_2 :=
forall (A: Type) (a: A) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (pu: Z) (un: Z) (list_pre: Z) (node_pre: Z) (list_pstPrev: Z),
  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (dllseg_shift storeA list_pre list_pstPrev l )
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (dllseg_shift storeA list_pre list_pstPrev l )
.

Definition LOS_ListTailInsert_which_implies_wit_1 :=
(
forall (A: Type) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (list: Z),
  (store_dll storeA list l )
|--
  EX (list_pstPrev: Z),
  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list)
  **  ((&((list)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (dllseg_shift storeA list list_pstPrev l )
) \/
(
forall (A: Type) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (list: Z),
  (store_dll storeA list l )
|--
  EX (list_pstPrev: Z),
  ((&((list_pstPrev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list)
  **  ((&((list)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pstPrev)
  **  (dllseg_shift storeA list list_pstPrev l )
).

(*----- Function LOS_ListHeadInsert -----*)

Definition LOS_ListHeadInsert_return_wit_1 :=
forall (A: Type) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (a: A) (list_pre: Z) (node_pre: Z),
  (store_dll storeA list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )
|--
  (store_dll storeA list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )
.

Definition LOS_ListHeadInsert_partial_solve_wit_1 :=
forall (A: Type) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (a: A) (pu: Z) (un: Z) (list_pre: Z) (node_pre: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
|--
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  (store_dll storeA list_pre l )
.

(* Shallow FunAssertion specs for LOS_ListAdd. *)
Definition LOS_ListAdd_sig : FuncSig := ([ * struct "LOS_DL_LIST";  * struct "LOS_DL_LIST"], void)%ctype.

Definition LOS_ListAdd_low_level_spec : Spec LOS_ListAdd_sig :=
  fun F =>
ALL A : Type,
ALL (storeA: (Z -> (A -> Assertion))),
ALL (a: A),
ALL (list_pstNext: Z),
HoareFun ([ * struct "LOS_DL_LIST";  * struct "LOS_DL_LIST"], void)%ctype
  (fun '(list_pre, node_pre) =>
  (EX (un: Z) (pu: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA node_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext)
  **  ((&((list_pstNext)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)))
  (fun '(list_pre, node_pre) (_retval : unit) =>
  (((&((list_pstNext)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext)
  **  (dllseg_shift storeA list_pre node_pre (cons ((Build_DL_Node (a) (node_pre))) ((@nil (@DL_Node A)))) )))
  F.

Definition LOS_ListAdd_high_level_spec : Spec LOS_ListAdd_sig :=
  fun F =>
ALL A : Type,
ALL (storeA1: (Z -> (A -> Assertion))),
ALL (l: (@list (@DL_Node A))),
ALL (a: A),
HoareFun ([ * struct "LOS_DL_LIST";  * struct "LOS_DL_LIST"], void)%ctype
  (fun '(list_pre, node_pre) =>
  (EX (un: Z) (pu: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA1 node_pre a )
  **  (store_dll storeA1 list_pre l )))
  (fun '(list_pre, node_pre) (_retval : unit) =>
  ((store_dll storeA1 list_pre (cons ((Build_DL_Node (a) (node_pre))) (l)) )))
  F.

Definition LOS_ListAdd_low_level_spec_entail_high_level_spec :=
forall (A: Type),
forall (list_pre: Z) (node_pre: Z) (storeA1_high_level_spec: (Z -> (A -> Assertion))) (l_high_level_spec: (@list (@DL_Node A))) (a_high_level_spec: A),
  (EX (un: Z) (pu: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un)
  **  (storeA1_high_level_spec node_pre a_high_level_spec )
  **  (store_dll storeA1_high_level_spec list_pre l_high_level_spec ))
|--
EX (A_2: Type) ,
EX (storeA_low_level_spec: (Z -> (A_2 -> Assertion)))(a_low_level_spec: A_2)(list_pstNext_low_level_spec: Z),
  (EX (un_2: Z) (pu_2: Z),
  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pu_2)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> un_2)
  **  (storeA_low_level_spec node_pre a_low_level_spec )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  ((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre))
  **
  (  (((&((list_pstNext_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pstNext_low_level_spec)
  **  (dllseg_shift storeA_low_level_spec list_pre node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) (nil)) ))
  -*
  ((store_dll storeA1_high_level_spec list_pre (cons ((Build_DL_Node (a_high_level_spec) (node_pre))) (l_high_level_spec)) )))
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListAdd_return_wit_1 : LOS_ListAdd_return_wit_1.
Axiom proof_of_LOS_ListTailInsert_return_wit_1 : LOS_ListTailInsert_return_wit_1.
Axiom proof_of_LOS_ListTailInsert_partial_solve_wit_1 : LOS_ListTailInsert_partial_solve_wit_1.
Axiom proof_of_LOS_ListTailInsert_partial_solve_wit_2 : LOS_ListTailInsert_partial_solve_wit_2.
Axiom proof_of_LOS_ListTailInsert_which_implies_wit_1 : LOS_ListTailInsert_which_implies_wit_1.
Axiom proof_of_LOS_ListHeadInsert_return_wit_1 : LOS_ListHeadInsert_return_wit_1.
Axiom proof_of_LOS_ListHeadInsert_partial_solve_wit_1 : LOS_ListHeadInsert_partial_solve_wit_1.
Axiom proof_of_LOS_ListAdd_low_level_spec_entail_high_level_spec : LOS_ListAdd_low_level_spec_entail_high_level_spec.

End VC_Correct.
