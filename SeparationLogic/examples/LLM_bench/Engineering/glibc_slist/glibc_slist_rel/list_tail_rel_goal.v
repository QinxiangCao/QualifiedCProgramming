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
Require Import list_tail_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function list_tail -----*)

Definition list_tail_safety_wit_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (list_tail_M (l1_low_level_spec)) X_low_level_spec )) (PreH2 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition list_tail_safety_wit_2 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (list_tail_M (l1_low_level_spec)) X_low_level_spec )) (PreH3 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
|--
  “ False ”
.

Definition list_tail_safety_wit_3 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x_2) (l0)))) (PreH2 : (safeExec ATrue (bind ((list_tail_M_loop (l1) (l2))) (list_tail_M_loop_end)) X_low_level_spec )) (PreH3 : (x <> 0)) (PreH4 : (x_pre <> 0)) (PreH5 : (x_pre <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sllseg x_pre x l1 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition list_tail_entail_wit_1 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_tail_M (l1_low_level_spec)) X_low_level_spec )) (PreH3 : (x_pre <> 0)) ,
  (sll x_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((list_tail_M_loop (l1) (l2))) (list_tail_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x_pre x_pre l1 )
  **  (sll x_pre l2 )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_tail_M (l1_low_level_spec)) X_low_level_spec )) (PreH3 : (x_pre <> 0)) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((list_tail_M_loop ((@nil Z)) (l1_low_level_spec))) (list_tail_M_loop_end)) X_low_level_spec ) ”
  &&  emp
).

Definition list_tail_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (list_tail_M (l1_low_level_spec)) X_low_level_spec )) (PreH3 : (x_pre <> 0)) ,
  (safeExec ATrue (bind ((list_tail_M_loop ((@nil Z)) (l1_low_level_spec))) (list_tail_M_loop_end)) X_low_level_spec )
.

Definition list_tail_entail_wit_2 := 
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (PreH1 : (y <> 0)) (PreH2 : (l2_2 = (cons (x_2) (l0)))) (PreH3 : (safeExec ATrue (bind ((list_tail_M_loop (l1_2) (l2_2))) (list_tail_M_loop_end)) X_low_level_spec )) (PreH4 : (x <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x_pre x l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((list_tail_M_loop (l1) (l2))) (list_tail_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x_pre y l1 )
  **  (sll y l2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (PreH1 : (x_2 <= INT_MAX)) (PreH2 : (x_2 >= INT_MIN)) (PreH3 : (y <> 0)) (PreH4 : (l2_2 = (cons (x_2) (l0)))) (PreH5 : (safeExec ATrue (bind ((list_tail_M_loop (l1_2) (l2_2))) (list_tail_M_loop_end)) X_low_level_spec )) (PreH6 : (x <> 0)) (PreH7 : (x_pre <> 0)) (PreH8 : (x_pre <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x_pre x l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((list_tail_M_loop (l1) (l0))) (list_tail_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (y <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sllseg x_pre y l1 )
).

Definition list_tail_return_wit_1 := 
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2_2: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (PreH1 : (y = 0)) (PreH2 : (l2_2 = (cons (x_2) (l0)))) (PreH3 : (safeExec ATrue (bind ((list_tail_M_loop (l1) (l2_2))) (list_tail_M_loop_end)) X_low_level_spec )) (PreH4 : (x <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x_pre x l1 )
|--
  EX (l2: (@list Z))  (v: Z) ,
  “ (safeExec ATrue (return ((maketuple (l2) (v)))) X_low_level_spec ) ” 
  &&  “ (x <> 0) ”
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg x_pre x l2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2_2: (@list Z)) (x_2: Z) (l0: (@list Z)) (y: Z) (PreH1 : (y = 0)) (PreH2 : (l2_2 = (cons (x_2) (l0)))) (PreH3 : (safeExec ATrue (bind ((list_tail_M_loop (l1) (l2_2))) (list_tail_M_loop_end)) X_low_level_spec )) (PreH4 : (x <> 0)) (PreH5 : (x_pre <> 0)) (PreH6 : (x_pre <> 0)) ,
  (sll y l0 )
  **  (sllseg x_pre x l1 )
|--
  EX (l2: (@list Z)) ,
  “ (y = 0) ” 
  &&  “ (safeExec ATrue (return ((maketuple (l2) (x_2)))) X_low_level_spec ) ” 
  &&  “ (x <> 0) ”
  &&  (sllseg x_pre x l2 )
).

Definition list_tail_partial_solve_wit_1 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((list_tail_M_loop (l1) (l2))) (list_tail_M_loop_end)) X_low_level_spec )) (PreH2 : (x <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (x_pre <> 0)) ,
  (sllseg x_pre x l1 )
  **  (sll x l2 )
|--
  EX (y: Z)  (l0: (@list Z))  (x_2: Z) ,
  “ (l2 = (cons (x_2) (l0))) ” 
  &&  “ (safeExec ATrue (bind ((list_tail_M_loop (l1) (l2))) (list_tail_M_loop_end)) X_low_level_spec ) ” 
  &&  “ (x <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (sllseg x_pre x l1 )
.

Definition list_tail_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l1_high_level_spec: (@list Z)) ,
  “ (x_pre <> 0) ”
  &&  (sll x_pre l1_high_level_spec )
|--
EX (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (list_tail_M (l1_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sll x_pre l1_low_level_spec ))
  **
  ((EX l2_2 v_2 retval_2,
  “ (safeExec ATrue (return ((maketuple (l2_2) (v_2)))) X_low_level_spec ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (sllseg x_pre retval_2 l2_2 ))
  -*
  (EX l2 v retval,
  “ (l1_high_level_spec = (app (l2) ((cons (v) (nil))))) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg x_pre retval l2 )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_list_tail_safety_wit_1 : list_tail_safety_wit_1.
Axiom proof_of_list_tail_safety_wit_2 : list_tail_safety_wit_2.
Axiom proof_of_list_tail_safety_wit_3 : list_tail_safety_wit_3.
Axiom proof_of_list_tail_entail_wit_1 : list_tail_entail_wit_1.
Axiom proof_of_list_tail_entail_wit_2 : list_tail_entail_wit_2.
Axiom proof_of_list_tail_return_wit_1 : list_tail_return_wit_1.
Axiom proof_of_list_tail_partial_solve_wit_1 : list_tail_partial_solve_wit_1.
Axiom proof_of_list_tail_derive_high_level_spec_by_low_level_spec : list_tail_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
