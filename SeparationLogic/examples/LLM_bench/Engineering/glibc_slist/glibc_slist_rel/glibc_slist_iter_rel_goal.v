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
Require Import glibc_slist_iter_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_iter -----*)

Definition glibc_slist_clean_iter_safety_wit_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_M (l1_low_level_spec)) X_low_level_spec )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_safety_wit_2 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (s: Z) (PreH1 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH2 : (range l1_low_level_spec )) ,
  ((( &( "sum" ) )) # Int  |-> s)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x_pre x l1 )
  **  (sll x l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_safety_wit_3 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_2: Z) (l1: (@list Z)) (l2: (@list Z)) (s: Z) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0)))) (PreH2 : (x_2 <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH4 : (range l1_low_level_spec )) ,
  ((&((x_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((x_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "sum" ) )) # Int  |-> s)
  **  ((( &( "x" ) )) # Ptr  |-> x_2)
  **  (sllseg x_pre x_2 l1 )
|--
  “ ((s + x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + x )) ”
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_2: Z) (l1: (@list Z)) (l2: (@list Z)) (s: Z) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0)))) (PreH2 : (x_2 <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH4 : (range l1_low_level_spec )) ,
  ((&((x_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((x_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "sum" ) )) # Int  |-> s)
  **  ((( &( "x" ) )) # Ptr  |-> x_2)
  **  (sllseg x_pre x_2 l1 )
|--
  “ ((s + x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + x )) ”
).

Definition glibc_slist_clean_iter_safety_wit_3_split_goal_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_2: Z) (l1: (@list Z)) (l2: (@list Z)) (s: Z) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0)))) (PreH2 : (x_2 <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH4 : (range l1_low_level_spec )) ,
  ((&((x_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((x_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "sum" ) )) # Int  |-> s)
  **  ((( &( "x" ) )) # Ptr  |-> x_2)
  **  (sllseg x_pre x_2 l1 )
|--
  “ ((s + x ) <= INT_MAX) ”
.

Definition glibc_slist_clean_iter_safety_wit_3_split_goal_2 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_2: Z) (l1: (@list Z)) (l2: (@list Z)) (s: Z) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0)))) (PreH2 : (x_2 <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH4 : (range l1_low_level_spec )) ,
  ((&((x_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((x_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "sum" ) )) # Int  |-> s)
  **  ((( &( "x" ) )) # Ptr  |-> x_2)
  **  (sllseg x_pre x_2 l1 )
|--
  “ ((INT_MIN) <= (s + x )) ”
.

Definition glibc_slist_clean_iter_entail_wit_1 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (0))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (range l1_low_level_spec ) ”
  &&  (sllseg x_pre x_pre l1 )
  **  (sll x_pre l2 )
) \/
(
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_M (l1_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop ((@nil Z)) (l1_low_level_spec) (0))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_entail_wit_1_split_goal_1 := 
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_M (l1_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop ((@nil Z)) (l1_low_level_spec) (0))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )
.

Definition glibc_slist_clean_iter_entail_wit_2 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (s: Z) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2_2 = (cons (x) (l0)))) (PreH2 : (x_2 <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1_2) (l2_2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH4 : (range l1_low_level_spec )) ,
  ((&((x_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((x_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x_pre x_2 l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) ((s + x )))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (range l1_low_level_spec ) ”
  &&  (sllseg x_pre y l1 )
  **  (sll y l2 )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_2: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (s: Z) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (l2_2 = (cons (x) (l0)))) (PreH4 : (x_2 <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1_2) (l2_2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH6 : (range l1_low_level_spec )) ,
  ((&((x_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((x_2)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x_pre x_2 l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l0) ((s + x )))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (range l1_low_level_spec ) ”
  &&  (sllseg x_pre y l1 )
).

Definition glibc_slist_clean_iter_return_wit_1 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2_2: (@list Z)) (s: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2_2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH3 : (range l1_low_level_spec )) ,
  (sllseg x_pre x l1 )
  **  (sll x l2_2 )
|--
  EX (l2: (@list Z))  (r: Z) ,
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ” 
  &&  “ (s = r) ”
  &&  (sll x_pre l2 )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2_2: (@list Z)) (s: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2_2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH3 : (range l1_low_level_spec )) ,
  (sllseg x_pre x l1 )
  **  (sll x l2_2 )
|--
  EX (l2: (@list Z)) ,
  “ (safeExec ATrue (return ((maketuple (l2) (s)))) X_low_level_spec ) ”
  &&  (sll x_pre l2 )
).

Definition glibc_slist_clean_iter_partial_solve_wit_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (s: Z) (PreH1 : (x <> 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec )) (PreH3 : (range l1_low_level_spec )) ,
  (sllseg x_pre x l1 )
  **  (sll x l2 )
|--
  EX (y: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l2 = (cons (x_2) (l0))) ” 
  &&  “ (x <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_M_loop (l1) (l2) (s))) (glibc_slist_clean_iter_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (range l1_low_level_spec ) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sll y l0 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg x_pre x l1 )
.

Definition glibc_slist_clean_iter_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l1_high_level_spec: (@list Z)) ,
  “ (range l1_high_level_spec ) ”
  &&  (sll x_pre l1_high_level_spec )
|--
EX (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) ,
  (“ (range l1_low_level_spec ) ” 
  &&  “ (safeExec ATrue (glibc_slist_clean_iter_M (l1_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec ))
  **
  ((EX l2 r retval_2,
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ” 
  &&  “ (retval_2 = r) ”
  &&  (sll x_pre l2 ))
  -*
  (EX retval,
  “ (retval = (list_sum (l1_high_level_spec))) ”
  &&  (sll x_pre l1_high_level_spec )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_iter_safety_wit_1 : glibc_slist_clean_iter_safety_wit_1.
Axiom proof_of_glibc_slist_clean_iter_safety_wit_2 : glibc_slist_clean_iter_safety_wit_2.
Axiom proof_of_glibc_slist_clean_iter_safety_wit_3 : glibc_slist_clean_iter_safety_wit_3.
Axiom proof_of_glibc_slist_clean_iter_entail_wit_1 : glibc_slist_clean_iter_entail_wit_1.
Axiom proof_of_glibc_slist_clean_iter_entail_wit_2 : glibc_slist_clean_iter_entail_wit_2.
Axiom proof_of_glibc_slist_clean_iter_return_wit_1 : glibc_slist_clean_iter_return_wit_1.
Axiom proof_of_glibc_slist_clean_iter_partial_solve_wit_1 : glibc_slist_clean_iter_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_iter_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_iter_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
