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
Require Import glibc_slist_multi_rev_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function rev_append_local -----*)

Definition rev_append_local_safety_wit_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (dst: Z) (src: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "src" ) )) # Ptr  |-> src)
  **  (sll src l1 )
  **  ((( &( "dst" ) )) # Ptr  |-> dst)
  **  (sll dst l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rev_append_local_entail_wit_1 := 
(
forall (dst_pre: Z) (src_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (rev_append_local_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll src_pre l1_low_level_spec )
  **  (sll dst_pre l2_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec ) ”
  &&  (sll src_pre l1 )
  **  (sll dst_pre l2 )
) \/
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (rev_append_local_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((rev_append_local_M_loop (l1_low_level_spec) (l2_low_level_spec))) (rev_append_local_M_loop_end)) X_low_level_spec ) ”
  &&  emp
).

Definition rev_append_local_entail_wit_1_split_goal_1 := 
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (rev_append_local_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((rev_append_local_M_loop (l1_low_level_spec) (l2_low_level_spec))) (rev_append_local_M_loop_end)) X_low_level_spec )
.

Definition rev_append_local_entail_wit_2 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (dst: Z) (src: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l1_2 = (cons (x) (l0)))) (PreH2 : (src <> 0)) (PreH3 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1_2) (l2_2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  ((&((src)  # "list" ->ₛ "next")) # Ptr  |-> dst)
  **  (sll y l0 )
  **  ((&((src)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "node" ) )) # Ptr  |-> src)
  **  (sll dst l2_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec ) ”
  &&  ((( &( "node" ) )) # Ptr  |->_)
  **  (sll y l1 )
  **  (sll src l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (src: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (l1_2 = (cons (x) (l0)))) (PreH2 : (src <> 0)) (PreH3 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1_2) (l2_2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((rev_append_local_M_loop (l0) ((cons (x) (l2_2))))) (rev_append_local_M_loop_end)) X_low_level_spec ) ”
  &&  emp
).

Definition rev_append_local_entail_wit_2_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (src: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (PreH1 : (l1_2 = (cons (x) (l0)))) (PreH2 : (src <> 0)) (PreH3 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1_2) (l2_2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((rev_append_local_M_loop (l0) ((cons (x) (l2_2))))) (rev_append_local_M_loop_end)) X_low_level_spec )
.

Definition rev_append_local_return_wit_1 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (dst: Z) (src: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (src = 0)) (PreH2 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  (sll src l1 )
  **  (sll dst l2 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll dst l3 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (src: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (src = 0)) (PreH2 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  (sll src l1 )
|--
  “ (safeExec ATrue (return (l2)) X_low_level_spec ) ”
  &&  emp
).

Definition rev_append_local_return_wit_1_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (src: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (src = 0)) (PreH2 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  (sll src l1 )
|--
  “ (safeExec ATrue (return (l2)) X_low_level_spec ) ”
.

Definition rev_append_local_return_wit_1_split_goal_spatial := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (src: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (src = 0)) (PreH2 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  (sll src l1 )
|--
  TT && emp 
.

Definition rev_append_local_partial_solve_wit_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (dst: Z) (src: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (src <> 0)) (PreH2 : (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec )) ,
  (sll src l1 )
  **  (sll dst l2 )
|--
  EX (y: Z)  (l0: (@list Z))  (x: Z) ,
  “ (l1 = (cons (x) (l0))) ” 
  &&  “ (src <> 0) ” 
  &&  “ (safeExec ATrue (bind ((rev_append_local_M_loop (l1) (l2))) (rev_append_local_M_loop_end)) X_low_level_spec ) ”
  &&  ((&((src)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y l0 )
  **  ((&((src)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll dst l2 )
.

(*----- Function glibc_slist_clean_multi_rev -----*)

Definition glibc_slist_clean_multi_rev_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_multi_rev_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_multi_rev_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_multi_rev_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll 0 (@nil Z) )
  **  (sll y_pre l2_low_level_spec )
) \/
(
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_multi_rev_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_multi_rev_entail_wit_1_split_goal_1 := 
forall (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_multi_rev_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec )
.

Definition glibc_slist_clean_multi_rev_entail_wit_2 := 
(
forall (y_pre: Z) (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec )) ,
  (sll retval l3_2 )
  **  (sll y_pre l2_low_level_spec )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3)) X_low_level_spec ) ”
  &&  (sll retval l3 )
  **  (sll y_pre l2_low_level_spec )
) \/
(
forall (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3_2)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_multi_rev_entail_wit_2_split_goal_1 := 
forall (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3_2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((return (l3_2))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec )) ,
  (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3_2)) X_low_level_spec )
.

Definition glibc_slist_clean_multi_rev_entail_wit_3 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l3: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (return (l3)) X_low_level_spec )) ,
  (sll retval l3 )
|--
  EX (l4: (@list Z)) ,
  “ (safeExec ATrue (return (l4)) X_low_level_spec ) ”
  &&  (sll retval l4 )
.

Definition glibc_slist_clean_multi_rev_return_wit_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (retval: Z) (l4: (@list Z)) (PreH1 : (safeExec ATrue (return (l4)) X_low_level_spec )) ,
  (sll retval l4 )
|--
  EX (l3: (@list Z)) ,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll retval l3 )
.

Definition glibc_slist_clean_multi_rev_partial_solve_wit_1_pure := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  (sll 0 (@nil Z) )
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec ) ”
.

Definition glibc_slist_clean_multi_rev_partial_solve_wit_1_aux := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
  **  (sll 0 (@nil Z) )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec) ((@nil Z)))) ((rev_append_local_M (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll 0 (@nil Z) )
  **  (sll y_pre l2_low_level_spec )
.

Definition glibc_slist_clean_multi_rev_partial_solve_wit_1 := glibc_slist_clean_multi_rev_partial_solve_wit_1_pure -> glibc_slist_clean_multi_rev_partial_solve_wit_1_aux.

Definition glibc_slist_clean_multi_rev_partial_solve_wit_2_pure := 
forall (y_pre: Z) (x_pre: Z) (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (retval: Z) (l3: (@list Z)) (PreH1 : (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3)) X_low_level_spec )) ,
  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (sll retval l3 )
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (sll y_pre l2_low_level_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3)) X_low_level_spec ) ”
.

Definition glibc_slist_clean_multi_rev_partial_solve_wit_2_aux := 
forall (y_pre: Z) (l2_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (retval: Z) (l3: (@list Z)) (PreH1 : (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3)) X_low_level_spec )) ,
  (sll retval l3 )
  **  (sll y_pre l2_low_level_spec )
|--
  “ (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3)) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (rev_append_local_M (l2_low_level_spec) (l3)) X_low_level_spec ) ”
  &&  (sll y_pre l2_low_level_spec )
  **  (sll retval l3 )
.

Definition glibc_slist_clean_multi_rev_partial_solve_wit_2 := glibc_slist_clean_multi_rev_partial_solve_wit_2_pure -> glibc_slist_clean_multi_rev_partial_solve_wit_2_aux.

Definition glibc_slist_clean_multi_rev_derive_high_level_spec_by_low_level_spec := 
forall (y_pre: Z) (x_pre: Z) (l2_high_level_spec: (@list Z)) (l1_high_level_spec: (@list Z)) ,
  (sll x_pre l1_high_level_spec )
  **  (sll y_pre l2_high_level_spec )
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (glibc_slist_clean_multi_rev_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec )
  **  (sll y_pre l2_low_level_spec ))
  **
  ((EX l3 retval_2,
  “ (safeExec ATrue (return (l3)) X_low_level_spec ) ”
  &&  (sll retval_2 l3 ))
  -*
  (EX retval,
  (sll retval (app ((rev (l2_high_level_spec))) ((rev (l1_high_level_spec)))) )))
.

Definition rev_append_local_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (dst_pre: Z) (src_pre: Z) (l2_low_level_spec_aux: (@list Z)) (l1_low_level_spec_aux: (@list Z)) (X_low_level_spec_aux: (B -> (unit -> Prop))) (cont_low_level_spec_aux: ((@list Z) -> (@ MonadErr.M  unit B))) ,
  “ (safeExec ATrue (bind ((rev_append_local_M (l1_low_level_spec_aux) (l2_low_level_spec_aux))) (cont_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll src_pre l1_low_level_spec_aux )
  **  (sll dst_pre l2_low_level_spec_aux )
|--
EX (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (rev_append_local_M (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll src_pre l1_low_level_spec )
  **  (sll dst_pre l2_low_level_spec ))
  **
  ((EX l3_2 retval_2,
  “ (safeExec ATrue (return (l3_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l3_2 ))
  -*
  (EX l3 retval,
  “ (safeExec ATrue (bind ((return (l3))) (cont_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll retval l3 )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_rev_append_local_safety_wit_1 : rev_append_local_safety_wit_1.
Axiom proof_of_rev_append_local_entail_wit_1 : rev_append_local_entail_wit_1.
Axiom proof_of_rev_append_local_entail_wit_2 : rev_append_local_entail_wit_2.
Axiom proof_of_rev_append_local_return_wit_1 : rev_append_local_return_wit_1.
Axiom proof_of_rev_append_local_partial_solve_wit_1 : rev_append_local_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_multi_rev_safety_wit_1 : glibc_slist_clean_multi_rev_safety_wit_1.
Axiom proof_of_glibc_slist_clean_multi_rev_entail_wit_1 : glibc_slist_clean_multi_rev_entail_wit_1.
Axiom proof_of_glibc_slist_clean_multi_rev_entail_wit_2 : glibc_slist_clean_multi_rev_entail_wit_2.
Axiom proof_of_glibc_slist_clean_multi_rev_entail_wit_3 : glibc_slist_clean_multi_rev_entail_wit_3.
Axiom proof_of_glibc_slist_clean_multi_rev_return_wit_1 : glibc_slist_clean_multi_rev_return_wit_1.
Axiom proof_of_glibc_slist_clean_multi_rev_partial_solve_wit_1_pure : glibc_slist_clean_multi_rev_partial_solve_wit_1_pure.
Axiom proof_of_glibc_slist_clean_multi_rev_partial_solve_wit_1 : glibc_slist_clean_multi_rev_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_multi_rev_partial_solve_wit_2_pure : glibc_slist_clean_multi_rev_partial_solve_wit_2_pure.
Axiom proof_of_glibc_slist_clean_multi_rev_partial_solve_wit_2 : glibc_slist_clean_multi_rev_partial_solve_wit_2.
Axiom proof_of_glibc_slist_clean_multi_rev_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_multi_rev_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_rev_append_local_derive_low_level_spec_aux_by_low_level_spec : rev_append_local_derive_low_level_spec_aux_by_low_level_spec.

End VC_Correct.
