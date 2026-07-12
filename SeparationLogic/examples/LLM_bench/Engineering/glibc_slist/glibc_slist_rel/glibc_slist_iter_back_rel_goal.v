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
Require Import glibc_slist_iter_back_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.

(*----- Function glibc_slist_clean_iter_back -----*)

Definition glibc_slist_clean_iter_back_safety_wit_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_safety_wit_2 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_safety_wit_3 := 
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ltail: (@list Z)) (x_next: Z) (r_2: Z) (retval: Z) (ltail_2: (@list Z)) (r: Z) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (ltail_2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (retval = r_2)) (PreH4 : (range ltail )) (PreH5 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "sum" ) )) # Int  |-> r)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail_2 )
|--
  “ ((r + v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + v )) ”
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ltail: (@list Z)) (x_next: Z) (r_2: Z) (retval: Z) (ltail_2: (@list Z)) (r: Z) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (ltail_2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (retval = r_2)) (PreH4 : (range ltail )) (PreH5 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "sum" ) )) # Int  |-> r)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail_2 )
|--
  “ ((r + v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + v )) ”
).

Definition glibc_slist_clean_iter_back_safety_wit_3_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ltail: (@list Z)) (x_next: Z) (r_2: Z) (retval: Z) (ltail_2: (@list Z)) (r: Z) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (ltail_2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (retval = r_2)) (PreH4 : (range ltail )) (PreH5 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "sum" ) )) # Int  |-> r)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail_2 )
|--
  “ ((r + v ) <= INT_MAX) ”
.

Definition glibc_slist_clean_iter_back_safety_wit_3_split_goal_2 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ltail: (@list Z)) (x_next: Z) (r_2: Z) (retval: Z) (ltail_2: (@list Z)) (r: Z) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (ltail_2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (retval = r_2)) (PreH4 : (range ltail )) (PreH5 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "sum" ) )) # Int  |-> r)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail_2 )
|--
  “ ((INT_MIN) <= (r + v )) ”
.

Definition glibc_slist_clean_iter_back_entail_wit_1 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre <> 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  EX (x_next: Z)  (v: Z)  (ltail: (@list Z)) ,
  “ (range ltail ) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l0: (@list Z)) (PreH1 : (l1_low_level_spec = (cons (x) (l0)))) (PreH2 : (x_pre <> 0)) (PreH3 : (range l1_low_level_spec )) (PreH4 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (l0))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (x)))) X_low_level_spec ) ” 
  &&  “ (range l0 ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l0: (@list Z)) (PreH1 : (l1_low_level_spec = (cons (x) (l0)))) (PreH2 : (x_pre <> 0)) (PreH3 : (range l1_low_level_spec )) (PreH4 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (l0))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (x)))) X_low_level_spec )
.

Definition glibc_slist_clean_iter_back_entail_wit_1_split_goal_2 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x: Z) (l0: (@list Z)) (PreH1 : (l1_low_level_spec = (cons (x) (l0)))) (PreH2 : (x_pre <> 0)) (PreH3 : (range l1_low_level_spec )) (PreH4 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  (range l0 )
.

Definition glibc_slist_clean_iter_back_entail_wit_2 := 
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (v_2: Z) (ltail: (@list Z)) (x_next: Z) (l2: (@list Z)) (r: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v_2)))) X_low_level_spec )) (PreH2 : (retval = r)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)) ,
  (sll x_next l2 )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
|--
  EX (ltail_2: (@list Z))  (v: Z) ,
  “ (safeExec ATrue (bind ((return ((maketuple (ltail_2) (retval))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (retval = r) ” 
  &&  “ (range ltail ) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail_2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (v_2: Z) (ltail: (@list Z)) (l2: (@list Z)) (r: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v_2)))) X_low_level_spec )) (PreH2 : (retval = r)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((return ((maketuple (l2) (retval))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v_2)))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (v_2: Z) (ltail: (@list Z)) (l2: (@list Z)) (r: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v_2)))) X_low_level_spec )) (PreH2 : (retval = r)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)) ,
  (safeExec ATrue (bind ((return ((maketuple (l2) (retval))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v_2)))) X_low_level_spec )
.

Definition glibc_slist_clean_iter_back_return_wit_1 := 
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ltail: (@list Z)) (x_next: Z) (r_3: Z) (retval: Z) (ltail_2: (@list Z)) (r_2: Z) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (ltail_2) (r_2))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (retval = r_3)) (PreH4 : (range ltail )) (PreH5 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail_2 )
|--
  EX (l2: (@list Z))  (r: Z) ,
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ” 
  &&  “ ((r_2 + v ) = r) ”
  &&  (sll x_pre l2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ltail: (@list Z)) (r_3: Z) (retval: Z) (ltail_2: (@list Z)) (r_2: Z) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (ltail_2) (r_2))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (retval = r_3)) (PreH4 : (range ltail )) (PreH5 : (x_pre <> 0)) ,
  TT && emp 
|--
  “ (safeExec ATrue (return ((maketuple ((cons (v) (ltail_2))) ((r_2 + v ))))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (ltail: (@list Z)) (r_3: Z) (retval: Z) (ltail_2: (@list Z)) (r_2: Z) (v: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (ltail_2) (r_2))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (retval = r_3)) (PreH4 : (range ltail )) (PreH5 : (x_pre <> 0)) ,
  (safeExec ATrue (return ((maketuple ((cons (v) (ltail_2))) ((r_2 + v ))))) X_low_level_spec )
.

Definition glibc_slist_clean_iter_back_return_wit_2 := 
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  EX (l2: (@list Z))  (r: Z) ,
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ” 
  &&  “ (0 = r) ”
  &&  (sll x_pre l2 )
) \/
(
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple ((@nil Z)) (0)))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple ((@nil Z)) (0)))) X_low_level_spec ) ”
.

Definition glibc_slist_clean_iter_back_return_wit_2_split_goal_spatial := 
forall (x_pre: Z) (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l1_low_level_spec )
|--
  TT && emp 
.

Definition glibc_slist_clean_iter_back_partial_solve_wit_1_pure := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (v: Z) (ltail: (@list Z)) (x_next: Z) (PreH1 : (range ltail )) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH3 : (x_pre <> 0)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "sum" ) )) # Int  |->_)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail )
|--
  “ (range ltail ) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec ) ”
.

Definition glibc_slist_clean_iter_back_partial_solve_wit_1_aux := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (v: Z) (ltail: (@list Z)) (x_next: Z) (PreH1 : (range ltail )) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH3 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail )
|--
  “ (range ltail ) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec ) ” 
  &&  “ (range ltail ) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ”
  &&  (sll x_next ltail )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
.

Definition glibc_slist_clean_iter_back_partial_solve_wit_1 := glibc_slist_clean_iter_back_partial_solve_wit_1_pure -> glibc_slist_clean_iter_back_partial_solve_wit_1_aux.

Definition glibc_slist_clean_iter_back_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l1_high_level_spec: (@list Z)) ,
  “ (range l1_high_level_spec ) ”
  &&  (sll x_pre l1_high_level_spec )
|--
EX (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) ,
  (“ (range l1_low_level_spec ) ” 
  &&  “ (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec ) ”
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

Definition glibc_slist_clean_iter_back_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (l1_low_level_spec_aux: (@list Z)) (X_low_level_spec_aux: (B -> (unit -> Prop))) (cont_low_level_spec_aux: (((@list Z) * Z) -> (@ MonadErr.M  unit B))) ,
  “ (range l1_low_level_spec_aux ) ” 
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (l1_low_level_spec_aux))) (cont_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l1_low_level_spec_aux )
|--
EX (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (l1_low_level_spec: (@list Z)) ,
  (“ (range l1_low_level_spec ) ” 
  &&  “ (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec ))
  **
  ((EX l2_2 r_2 retval_2,
  “ (safeExec ATrue (return ((maketuple (l2_2) (r_2)))) X_low_level_spec ) ” 
  &&  “ (retval_2 = r_2) ”
  &&  (sll x_pre l2_2 ))
  -*
  (EX l2 r retval,
  “ (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) (cont_low_level_spec_aux)) X_low_level_spec_aux ) ” 
  &&  “ (retval = r) ”
  &&  (sll x_pre l2 )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.
Include sll_Strategy_Correct.

Axiom proof_of_glibc_slist_clean_iter_back_safety_wit_1 : glibc_slist_clean_iter_back_safety_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_safety_wit_2 : glibc_slist_clean_iter_back_safety_wit_2.
Axiom proof_of_glibc_slist_clean_iter_back_safety_wit_3 : glibc_slist_clean_iter_back_safety_wit_3.
Axiom proof_of_glibc_slist_clean_iter_back_entail_wit_1 : glibc_slist_clean_iter_back_entail_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_entail_wit_2 : glibc_slist_clean_iter_back_entail_wit_2.
Axiom proof_of_glibc_slist_clean_iter_back_return_wit_1 : glibc_slist_clean_iter_back_return_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_return_wit_2 : glibc_slist_clean_iter_back_return_wit_2.
Axiom proof_of_glibc_slist_clean_iter_back_partial_solve_wit_1_pure : glibc_slist_clean_iter_back_partial_solve_wit_1_pure.
Axiom proof_of_glibc_slist_clean_iter_back_partial_solve_wit_1 : glibc_slist_clean_iter_back_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_iter_back_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_glibc_slist_clean_iter_back_derive_low_level_spec_aux_by_low_level_spec : glibc_slist_clean_iter_back_derive_low_level_spec_aux_by_low_level_spec.

End VC_Correct.
