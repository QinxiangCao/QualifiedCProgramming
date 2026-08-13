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

(*----- Function OsGetSortLinkAttribute -----*)

Definition OsGetSortLinkAttribute_safety_wit_1 := 
forall (type_pre: Z) (u: Z) (PreH1 : (( &( "g_taskSortLink" ) ) <> 0)) (PreH2 : (( &( "g_swtmrSortLink" ) ) <> 0)) (PreH3 : (type_pre = u)) ,
  ((( &( "type" ) )) # Int  |-> type_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OsGetSortLinkAttribute_safety_wit_2 := 
forall (type_pre: Z) (u: Z) (PreH1 : (type_pre <> 1)) (PreH2 : (( &( "g_taskSortLink" ) ) <> 0)) (PreH3 : (( &( "g_swtmrSortLink" ) ) <> 0)) (PreH4 : (type_pre = u)) ,
  ((( &( "type" ) )) # Int  |-> type_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition OsGetSortLinkAttribute_safety_wit_3 := 
forall (type_pre: Z) (u: Z) (PreH1 : (type_pre <> 2)) (PreH2 : (type_pre <> 1)) (PreH3 : (( &( "g_taskSortLink" ) ) <> 0)) (PreH4 : (( &( "g_swtmrSortLink" ) ) <> 0)) (PreH5 : (type_pre = u)) ,
  ((( &( "type" ) )) # Int  |-> type_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OsGetSortLinkAttribute_return_wit_1 := 
forall (type_pre: Z) (u: Z) (PreH1 : (type_pre <> 2)) (PreH2 : (type_pre <> 1)) (PreH3 : (( &( "g_taskSortLink" ) ) <> 0)) (PreH4 : (( &( "g_swtmrSortLink" ) ) <> 0)) (PreH5 : (type_pre = u)) ,
  TT && emp 
|--
  “ (u <> 1) ” 
  &&  “ (u <> 2) ” 
  &&  “ (0 = 0) ” 
  &&  “ (type_pre = u) ”
  &&  emp
.

Definition OsGetSortLinkAttribute_return_wit_2 := 
forall (type_pre: Z) (u: Z) (PreH1 : (type_pre = 2)) (PreH2 : (type_pre <> 1)) (PreH3 : (( &( "g_taskSortLink" ) ) <> 0)) (PreH4 : (( &( "g_swtmrSortLink" ) ) <> 0)) (PreH5 : (type_pre = u)) ,
  TT && emp 
|--
  “ (u = 2) ” 
  &&  “ (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) ” 
  &&  “ (type_pre = u) ”
  &&  emp
.

Definition OsGetSortLinkAttribute_return_wit_3 := 
forall (type_pre: Z) (u: Z) (PreH1 : (type_pre = 1)) (PreH2 : (( &( "g_taskSortLink" ) ) <> 0)) (PreH3 : (( &( "g_swtmrSortLink" ) ) <> 0)) (PreH4 : (type_pre = u)) ,
  TT && emp 
|--
  “ (u = 1) ” 
  &&  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ” 
  &&  “ (type_pre = u) ”
  &&  emp
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsGetSortLinkAttribute_safety_wit_1 : OsGetSortLinkAttribute_safety_wit_1.
Axiom proof_of_OsGetSortLinkAttribute_safety_wit_2 : OsGetSortLinkAttribute_safety_wit_2.
Axiom proof_of_OsGetSortLinkAttribute_safety_wit_3 : OsGetSortLinkAttribute_safety_wit_3.
Axiom proof_of_OsGetSortLinkAttribute_return_wit_1 : OsGetSortLinkAttribute_return_wit_1.
Axiom proof_of_OsGetSortLinkAttribute_return_wit_2 : OsGetSortLinkAttribute_return_wit_2.
Axiom proof_of_OsGetSortLinkAttribute_return_wit_3 : OsGetSortLinkAttribute_return_wit_3.

End VC_Correct.
