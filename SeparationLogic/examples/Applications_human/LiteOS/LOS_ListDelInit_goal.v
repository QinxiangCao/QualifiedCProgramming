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
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_goal.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_proof.

(*----- Function LOS_ListDelInit -----*)

Definition LOS_ListDelInit_return_wit_1 := 
(
forall (A: Type) (list_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
  **  (storeA list_pre a )
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
  **  (storeA list_pre a )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
) \/
(
forall (A: Type) (list_pre: Z) (storeA: (Z -> (A -> Assertion))) ,
  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
|--
  TT && emp 
).

Definition LOS_ListDelInit_return_wit_1_split_goal_spatial := 
forall (A: Type) (list_pre: Z) (storeA: (Z -> (A -> Assertion))) ,
  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
|--
  TT && emp 
.

Definition LOS_ListDelInit_partial_solve_wit_1 := 
forall (A: Type) (list_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  (dllseg_shift storeA prev list_pre (cons ((Build_DL_Node (a) (list_pre))) ((@nil (@DL_Node A)))) )
|--
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  (storeA list_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
.

Definition LOS_ListDelInit_partial_solve_wit_2 := 
forall (A: Type) (list_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  (dllseg_shift storeA prev list_pre (cons ((Build_DL_Node (a) (list_pre))) ((@nil (@DL_Node A)))) )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
  **  (storeA list_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
.

Definition LOS_ListDelInit_partial_solve_wit_3 := 
forall (A: Type) (list_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  (dllseg_shift storeA prev list_pre (cons ((Build_DL_Node (a) (list_pre))) ((@nil (@DL_Node A)))) )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (storeA list_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
.

Definition LOS_ListDelInit_partial_solve_wit_4 := 
forall (A: Type) (list_pre: Z) (next: Z) (prev: Z) (a: A) (storeA: (Z -> (A -> Assertion))) ,
  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
  **  (storeA list_pre a )
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
|--
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |->_)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
  **  ((&((prev)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next)
  **  (dllseg_shift storeA list_pre list_pre (@nil (@DL_Node A)) )
  **  (storeA list_pre a )
  **  ((&((next)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> prev)
.

Definition LOS_ListDelete_derive_mid_level_spec_by_low_level_spec := 
forall (A: Type) ,
forall (node_pre: Z) (l2_mid_level_spec: (@list (@DL_Node A))) (l1_mid_level_spec: (@list (@DL_Node A))) (a_mid_level_spec: A) (p_mid_level_spec: Z) (storeA1_mid_level_spec: (Z -> (A -> Assertion))) ,
  (store_dll storeA1_mid_level_spec p_mid_level_spec (app (l1_mid_level_spec) ((cons ((Build_DL_Node (a_mid_level_spec) (node_pre))) (l2_mid_level_spec)))) )
|--
EX (A: Type) ,
EX (storeA_low_level_spec: (Z -> (A -> Assertion))) (a_low_level_spec: A) (prev_low_level_spec: Z) (next_low_level_spec: Z) ,
  (((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> next_low_level_spec)
  **  ((&((next_low_level_spec)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> node_pre)
  **  (dllseg_shift storeA_low_level_spec prev_low_level_spec node_pre (cons ((Build_DL_Node (a_low_level_spec) (node_pre))) (nil)) ))
  **
  ((((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |->_)
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

Axiom proof_of_LOS_ListDelInit_return_wit_1 : LOS_ListDelInit_return_wit_1.
Axiom proof_of_LOS_ListDelInit_partial_solve_wit_1 : LOS_ListDelInit_partial_solve_wit_1.
Axiom proof_of_LOS_ListDelInit_partial_solve_wit_2 : LOS_ListDelInit_partial_solve_wit_2.
Axiom proof_of_LOS_ListDelInit_partial_solve_wit_3 : LOS_ListDelInit_partial_solve_wit_3.
Axiom proof_of_LOS_ListDelInit_partial_solve_wit_4 : LOS_ListDelInit_partial_solve_wit_4.
Axiom proof_of_LOS_ListDelete_derive_mid_level_spec_by_low_level_spec : LOS_ListDelete_derive_mid_level_spec_by_low_level_spec.

End VC_Correct.
