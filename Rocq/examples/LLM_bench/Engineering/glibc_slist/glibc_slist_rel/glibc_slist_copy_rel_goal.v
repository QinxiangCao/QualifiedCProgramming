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
Require Import glibc_slist_copy_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_copy -----*)

Definition glibc_slist_clean_copy_safety_wit_1 := 
forall (src_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_copy_M (l1_low_level_spec)) X_low_level_spec )) ,
  ((( &( "copy" ) )) # Ptr  |->_)
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "dst" ) )) # Ptr  |->_)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  (sll src_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_copy_safety_wit_2 := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "copy" ) )) # Ptr  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (sllseg src_pre node l1 )
  **  (sll node l2 )
  **  ((( &( "dst" ) )) # Ptr  |-> dst)
  **  (sll dst l3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_copy_safety_wit_3 := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (l2 = (cons (x) (l0)))) (PreH4 : (node <> 0)) (PreH5 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "copy" ) )) # Ptr  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (sllseg src_pre node l1 )
  **  ((( &( "dst" ) )) # Ptr  |-> dst)
  **  (sll dst l3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_copy_safety_wit_4 := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_next = 0)) (PreH4 : (l2 = (cons (x) (l0)))) (PreH5 : (node <> 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "copy" ) )) # Ptr  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (sllseg src_pre node l1 )
  **  ((( &( "dst" ) )) # Ptr  |-> dst)
  **  (sll dst l3 )
|--
  “ False ”
.

Definition glibc_slist_clean_copy_entail_wit_1 := 
(
forall (src_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_copy_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sll src_pre l1_low_level_spec )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec ) ”
  &&  (sllseg src_pre src_pre l1 )
  **  (sll src_pre l2 )
  **  (sll 0 l3 )
) \/
(
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_copy_M (l1_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop ((@nil Z)) (l1_low_level_spec) ((@nil Z)))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_copy_entail_wit_1_split_goal_1 := 
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (PreH1 : (safeExec ATrue (glibc_slist_clean_copy_M (l1_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop ((@nil Z)) (l1_low_level_spec) ((@nil Z)))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )
.

Definition glibc_slist_clean_copy_entail_wit_2 := 
(
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_next = 0)) (PreH4 : (l2 = (cons (x) (l0)))) (PreH5 : (node <> 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg src_pre node l1 )
  **  (sll dst l3 )
|--
  EX (ldst: (@list Z))  (lprefix: (@list Z))  (v: Z)  (lrest: (@list Z)) ,
  “ (safeExec ATrue (bind ((list_append_raw_M (ldst) ((cons (v) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec ) ” 
  &&  “ (node <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (node <> 0) ”
  &&  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg src_pre node lprefix )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y lrest )
  **  (sll dst ldst )
  **  (sll retval (cons (v) ((@nil Z))) )
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_next = 0)) (PreH4 : (l2 = (cons (x) (l0)))) (PreH5 : (node <> 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (l3) ((cons (x) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (l1) (x) (l0)))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_copy_entail_wit_2_split_goal_1 := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval_next = 0)) (PreH4 : (l2 = (cons (x) (l0)))) (PreH5 : (node <> 0)) (PreH6 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((list_append_raw_M (l3) ((cons (x) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (l1) (x) (l0)))) X_low_level_spec )
.

Definition glibc_slist_clean_copy_entail_wit_3 := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (node: Z) (l2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval: Z) (lprefix_2: (@list Z)) (v_2: Z) (lrest_2: (@list Z)) (l3: (@list Z)) (retval_2: Z) (PreH1 : (safeExec ATrue (bind ((return (l3))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix_2) (v_2) (lrest_2)))) X_low_level_spec )) (PreH2 : (node <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval_next = 0)) (PreH7 : (l2 = (cons (x) (l0)))) (PreH8 : (node <> 0)) ,
  (sll retval_2 l3 )
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (sllseg src_pre node lprefix_2 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y lrest_2 )
|--
  EX (ldst: (@list Z))  (lprefix: (@list Z))  (v: Z)  (lrest: (@list Z)) ,
  “ (safeExec ATrue (bind ((return (ldst))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec ) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (node <> 0) ”
  &&  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg src_pre node lprefix )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y lrest )
  **  (sll retval_2 ldst )
.

Definition glibc_slist_clean_copy_entail_wit_4 := 
(
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (node: Z) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval_2: Z) (retval: Z) (ldst: (@list Z)) (lprefix: (@list Z)) (v: Z) (lrest: (@list Z)) (PreH1 : (safeExec ATrue (bind ((return (ldst))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec )) (PreH2 : (node <> 0)) (PreH3 : (node <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_next = 0)) (PreH8 : (l2_2 = (cons (x) (l0)))) (PreH9 : (node <> 0)) ,
  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg src_pre node lprefix )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y lrest )
  **  (sll retval ldst )
  **  ((( &( "copy" ) )) # Ptr  |-> retval_2)
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec ) ”
  &&  ((( &( "copy" ) )) # Ptr  |->_)
  **  (sllseg src_pre y l1 )
  **  (sll y l2 )
  **  (sll retval l3 )
) \/
(
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (node: Z) (l2_2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval_2: Z) (ldst: (@list Z)) (lprefix: (@list Z)) (v: Z) (lrest: (@list Z)) (PreH1 : (v <= INT_MAX)) (PreH2 : (v >= INT_MIN)) (PreH3 : (safeExec ATrue (bind ((return (ldst))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec )) (PreH4 : (node <> 0)) (PreH5 : (node <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 <> 0)) (PreH9 : (retval_next = 0)) (PreH10 : (l2_2 = (cons (x) (l0)))) (PreH11 : (node <> 0)) ,
  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg src_pre node lprefix )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
|--
  EX (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (lrest) (ldst))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec ) ”
  &&  (sllseg src_pre y l1 )
).

Definition glibc_slist_clean_copy_return_wit_1 := 
(
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (node = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2_2) (l3_2))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  (sllseg src_pre node l1 )
  **  (sll node l2_2 )
  **  (sll dst l3_2 )
|--
  EX (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (return ((maketuple (l2) (l3)))) X_low_level_spec ) ”
  &&  (sll src_pre l2 )
  **  (sll dst l3 )
) \/
(
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (node: Z) (l1: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (node = 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2_2) (l3_2))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  (sllseg src_pre node l1 )
  **  (sll node l2_2 )
|--
  EX (l2: (@list Z)) ,
  “ (safeExec ATrue (return ((maketuple (l2) (l3_2)))) X_low_level_spec ) ”
  &&  (sll src_pre l2 )
).

Definition glibc_slist_clean_copy_partial_solve_wit_1 := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (node <> 0)) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  (sllseg src_pre node l1 )
  **  (sll node l2 )
  **  (sll dst l3 )
|--
  EX (x: Z)  (l0: (@list Z))  (y: Z) ,
  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec ) ”
  &&  ((&((node)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg src_pre node l1 )
  **  (sll dst l3 )
.

Definition glibc_slist_clean_copy_partial_solve_wit_2_pure := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0)))) (PreH2 : (node <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  ((&((node)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "copy" ) )) # Ptr  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  (sllseg src_pre node l1 )
  **  ((( &( "dst" ) )) # Ptr  |-> dst)
  **  (sll dst l3 )
|--
  “ (x = x) ”
.

Definition glibc_slist_clean_copy_partial_solve_wit_2_aux := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (PreH1 : (l2 = (cons (x) (l0)))) (PreH2 : (node <> 0)) (PreH3 : (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec )) ,
  ((&((node)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg src_pre node l1 )
  **  (sll dst l3 )
|--
  “ (x = x) ” 
  &&  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_copy_M_loop (l1) (l2) (l3))) (glibc_slist_clean_copy_M_after_loop)) X_low_level_spec ) ”
  &&  ((&((node)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (sll y l0 )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sllseg src_pre node l1 )
  **  (sll dst l3 )
.

Definition glibc_slist_clean_copy_partial_solve_wit_2 := glibc_slist_clean_copy_partial_solve_wit_2_pure -> glibc_slist_clean_copy_partial_solve_wit_2_aux.

Definition glibc_slist_clean_copy_partial_solve_wit_3_pure := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval: Z) (ldst: (@list Z)) (lprefix: (@list Z)) (v: Z) (lrest: (@list Z)) (PreH1 : (safeExec ATrue (bind ((list_append_raw_M (ldst) ((cons (v) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec )) (PreH2 : (node <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval_next = 0)) (PreH7 : (l2 = (cons (x) (l0)))) (PreH8 : (node <> 0)) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "copy" ) )) # Ptr  |-> retval)
  **  (sllseg src_pre node lprefix )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y lrest )
  **  ((( &( "dst" ) )) # Ptr  |-> dst)
  **  (sll dst ldst )
  **  (sll retval (cons (v) ((@nil Z))) )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (ldst) ((cons (v) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec ) ”
.

Definition glibc_slist_clean_copy_partial_solve_wit_3_aux := 
forall (src_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (dst: Z) (node: Z) (l2: (@list Z)) (x: Z) (l0: (@list Z)) (y: Z) (retval_next: Z) (retval: Z) (ldst: (@list Z)) (lprefix: (@list Z)) (v: Z) (lrest: (@list Z)) (PreH1 : (safeExec ATrue (bind ((list_append_raw_M (ldst) ((cons (v) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec )) (PreH2 : (node <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval_next = 0)) (PreH7 : (l2 = (cons (x) (l0)))) (PreH8 : (node <> 0)) ,
  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg src_pre node lprefix )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y lrest )
  **  (sll dst ldst )
  **  (sll retval (cons (v) ((@nil Z))) )
|--
  “ (safeExec ATrue (bind ((list_append_raw_M (ldst) ((cons (v) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (bind ((list_append_raw_M (ldst) ((cons (v) ((@nil Z)))))) ((residual_prog_in_glibc_slist_clean_copy_M_call_1 (lprefix) (v) (lrest)))) X_low_level_spec ) ” 
  &&  “ (node <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (l2 = (cons (x) (l0))) ” 
  &&  “ (node <> 0) ”
  &&  (sll dst ldst )
  **  (sll retval (cons (v) ((@nil Z))) )
  **  ((&((node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (sllseg src_pre node lprefix )
  **  ((&((node)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (sll y lrest )
.

Definition glibc_slist_clean_copy_partial_solve_wit_3 := glibc_slist_clean_copy_partial_solve_wit_3_pure -> glibc_slist_clean_copy_partial_solve_wit_3_aux.

Definition glibc_slist_clean_copy_derive_high_level_spec_by_low_level_spec := 
forall (src_pre: Z) (l1_high_level_spec: (@list Z)) ,
  (sll src_pre l1_high_level_spec )
|--
EX (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) ,
  (“ (safeExec ATrue (glibc_slist_clean_copy_M (l1_low_level_spec)) X_low_level_spec ) ”
  &&  (sll src_pre l1_low_level_spec ))
  **
  ((EX l2_2 l3 retval_2,
  “ (safeExec ATrue (return ((maketuple (l2_2) (l3)))) X_low_level_spec ) ”
  &&  (sll src_pre l2_2 )
  **  (sll retval_2 l3 ))
  -*
  (EX l2 retval,
  “ (glibc_slist_clean_copy_result l1_high_level_spec l2 ) ”
  &&  (sll src_pre l1_high_level_spec )
  **  (sll retval l2 )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_copy_safety_wit_1 : glibc_slist_clean_copy_safety_wit_1.
Axiom proof_of_glibc_slist_clean_copy_safety_wit_2 : glibc_slist_clean_copy_safety_wit_2.
Axiom proof_of_glibc_slist_clean_copy_safety_wit_3 : glibc_slist_clean_copy_safety_wit_3.
Axiom proof_of_glibc_slist_clean_copy_safety_wit_4 : glibc_slist_clean_copy_safety_wit_4.
Axiom proof_of_glibc_slist_clean_copy_entail_wit_1 : glibc_slist_clean_copy_entail_wit_1.
Axiom proof_of_glibc_slist_clean_copy_entail_wit_2 : glibc_slist_clean_copy_entail_wit_2.
Axiom proof_of_glibc_slist_clean_copy_entail_wit_3 : glibc_slist_clean_copy_entail_wit_3.
Axiom proof_of_glibc_slist_clean_copy_entail_wit_4 : glibc_slist_clean_copy_entail_wit_4.
Axiom proof_of_glibc_slist_clean_copy_return_wit_1 : glibc_slist_clean_copy_return_wit_1.
Axiom proof_of_glibc_slist_clean_copy_partial_solve_wit_1 : glibc_slist_clean_copy_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_copy_partial_solve_wit_2_pure : glibc_slist_clean_copy_partial_solve_wit_2_pure.
Axiom proof_of_glibc_slist_clean_copy_partial_solve_wit_2 : glibc_slist_clean_copy_partial_solve_wit_2.
Axiom proof_of_glibc_slist_clean_copy_partial_solve_wit_3_pure : glibc_slist_clean_copy_partial_solve_wit_3_pure.
Axiom proof_of_glibc_slist_clean_copy_partial_solve_wit_3 : glibc_slist_clean_copy_partial_solve_wit_3.
Axiom proof_of_glibc_slist_clean_copy_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_copy_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
