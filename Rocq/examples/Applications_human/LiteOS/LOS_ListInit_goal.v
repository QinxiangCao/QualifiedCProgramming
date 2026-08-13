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

(*----- Function LOS_ListInit -----*)

Definition LOS_ListInit_return_wit_1 := 
(
forall (A: Type) (list_pre: Z) (storeA: (Z -> (A -> Assertion))) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
|--
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
) \/
(
forall (A: Type) (list_pre: Z) (storeA: (Z -> (A -> Assertion))) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
|--
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
).

Definition LOS_ListInit_return_wit_1_split_goal_spatial := 
forall (A: Type) (list_pre: Z) (storeA: (Z -> (A -> Assertion))) ,
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
|--
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListInit_return_wit_1 : LOS_ListInit_return_wit_1.

End VC_Correct.
