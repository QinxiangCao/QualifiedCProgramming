From SimpleC.Verification Require Import VCPrelude.
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
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (range l1_low_level_spec )) (PreH2 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_safety_wit_2 :=
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l1_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition glibc_slist_clean_iter_back_safety_wit_3 :=
(
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (x_next: Z) (l2: (@list Z)) (r: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (retval = r)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)),
  (sll x_next l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "sum" ) )) # Int  |-> retval)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
|--
  “ ((retval + v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval + v )) ”
) \/
(
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (x_next: Z) (l2: (@list Z)) (r: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (retval = r)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)),
  (sll x_next l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "sum" ) )) # Int  |-> retval)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
|--
  “ ((retval + v ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (retval + v )) ”
).

Definition glibc_slist_clean_iter_back_safety_wit_3_split_goal_1 :=
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (x_next: Z) (l2: (@list Z)) (r: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (retval = r)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)),
  (sll x_next l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "sum" ) )) # Int  |-> retval)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
|--
  “ ((retval + v ) <= INT_MAX) ”
.

Definition glibc_slist_clean_iter_back_safety_wit_3_split_goal_2 :=
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (x_next: Z) (l2: (@list Z)) (r: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (retval = r)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)),
  (sll x_next l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "sum" ) )) # Int  |-> retval)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
|--
  “ ((INT_MIN) <= (retval + v )) ”
.

Definition glibc_slist_clean_iter_back_entail_wit_1 :=
(
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  EX (x_next: Z) (v: Z) (ltail: (@list Z)),
  “ (range ltail ) ”
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec ) ”
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next ltail )
) \/
(
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (x: Z) (l0: (@list Z)) (PreH1 : (l1_low_level_spec = (cons (x) (l0)))) (PreH2 : (x_pre <> 0)) (PreH3 : (range l1_low_level_spec )) (PreH4 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (l0))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (x)))) X_low_level_spec ) ”
  &&  “ (range l0 ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_entail_wit_1_split_goal_1 :=
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (x: Z) (l0: (@list Z)) (PreH1 : (l1_low_level_spec = (cons (x) (l0)))) (PreH2 : (x_pre <> 0)) (PreH3 : (range l1_low_level_spec )) (PreH4 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (l0))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (x)))) X_low_level_spec )
.

Definition glibc_slist_clean_iter_back_entail_wit_1_split_goal_2 :=
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (x: Z) (l0: (@list Z)) (PreH1 : (l1_low_level_spec = (cons (x) (l0)))) (PreH2 : (x_pre <> 0)) (PreH3 : (range l1_low_level_spec )) (PreH4 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  (range l0 )
.

Definition glibc_slist_clean_iter_back_return_wit_1 :=
(
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (x_next: Z) (l2_2: (@list Z)) (r_2: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2_2) (r_2))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (retval = r_2)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)),
  (sll x_next l2_2 )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
|--
  EX (l2: (@list Z)) (r: Z),
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ”
  &&  “ ((retval + v ) = r) ”
  &&  (sll x_pre l2 )
) \/
(
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (l2_2: (@list Z)) (r_2: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2_2) (r_2))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (retval = r_2)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)),
  TT && emp 
|--
  “ (safeExec ATrue (return ((maketuple ((cons (v) (l2_2))) ((r_2 + v ))))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_return_wit_1_split_goal_1 :=
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (l2_2: (@list Z)) (r_2: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((return ((maketuple (l2_2) (r_2))))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH2 : (retval = r_2)) (PreH3 : (range ltail )) (PreH4 : (x_pre <> 0)),
  (safeExec ATrue (return ((maketuple ((cons (v) (l2_2))) ((r_2 + v ))))) X_low_level_spec )
.

Definition glibc_slist_clean_iter_back_return_wit_2 :=
(
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  EX (l2: (@list Z)) (r: Z),
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ”
  &&  “ (0 = r) ”
  &&  (sll x_pre l2 )
) \/
(
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple ((@nil Z)) (0)))) X_low_level_spec ) ”
  &&  emp
).

Definition glibc_slist_clean_iter_back_return_wit_2_split_goal_1 :=
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple ((@nil Z)) (0)))) X_low_level_spec ) ”
.

Definition glibc_slist_clean_iter_back_return_wit_2_split_goal_spatial :=
forall (l1_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (range l1_low_level_spec )) (PreH3 : (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec )),
  (sll x_pre l1_low_level_spec )
|--
  TT && emp 
.

Definition glibc_slist_clean_iter_back_partial_solve_wit_1_pure :=
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (x_next: Z) (PreH1 : (range ltail )) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH3 : (x_pre <> 0)),
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
forall (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop))) (x_pre: Z) (v: Z) (ltail: (@list Z)) (x_next: Z) (PreH1 : (range ltail )) (PreH2 : (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (ltail))) ((residual_prog_in_glibc_slist_clean_iter_back_M_call_1 (v)))) X_low_level_spec )) (PreH3 : (x_pre <> 0)),
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

(* Shallow FunAssertion specs for glibc_slist_clean_iter_back. *)
Definition glibc_slist_clean_iter_back_sig : FuncSig := ([ * struct "list"], i32)%ctype.

Definition glibc_slist_clean_iter_back_low_level_spec : Spec glibc_slist_clean_iter_back_sig :=
  fun F =>
ALL (X: (((@list Z) * Z) -> (unit -> Prop))),
ALL (l1: (@list Z)),
HoareFun ([ * struct "list"], i32)%ctype
  (fun x_pre =>
  (“ (range l1 ) ”
  &&  “ (safeExec ATrue (glibc_slist_clean_iter_back_M (l1)) X ) ”
  &&  (sll x_pre l1 )))
  (fun x_pre retval =>
  (EX (l2: (@list Z)) (r: Z),
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X ) ”
  &&  “ (retval = r) ”
  &&  (sll x_pre l2 )))
  F.

Definition glibc_slist_clean_iter_back_high_level_spec : Spec glibc_slist_clean_iter_back_sig :=
  fun F =>
ALL (l1: (@list Z)),
HoareFun ([ * struct "list"], i32)%ctype
  (fun x_pre =>
  (“ (range l1 ) ”
  &&  (sll x_pre l1 )))
  (fun x_pre retval =>
  (“ (retval = (list_sum (l1))) ”
  &&  (sll x_pre l1 )))
  F.

Definition glibc_slist_clean_iter_back_low_level_spec_aux : Spec glibc_slist_clean_iter_back_sig :=
  fun F =>
ALL B : Type,
ALL (cont: (((@list Z) * Z) -> (@ MonadErr.M  unit B))),
ALL (X: (B -> (unit -> Prop))),
ALL (l1: (@list Z)),
HoareFun ([ * struct "list"], i32)%ctype
  (fun x_pre =>
  (“ (range l1 ) ”
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (l1))) (cont)) X ) ”
  &&  (sll x_pre l1 )))
  (fun x_pre retval =>
  (EX (l2: (@list Z)) (r: Z),
  “ (safeExec ATrue (bind ((return ((maketuple (l2) (r))))) (cont)) X ) ”
  &&  “ (retval = r) ”
  &&  (sll x_pre l2 )))
  F.

Definition glibc_slist_clean_iter_back_low_level_spec_entail_high_level_spec :=
forall (x_pre: Z) (l1_high_level_spec: (@list Z)),
  (“ (range l1_high_level_spec ) ”
  &&  (sll x_pre l1_high_level_spec ))
|--
EX (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop)))(l1_low_level_spec: (@list Z)),
  (“ (range l1_low_level_spec ) ”
  &&  “ (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l2: (@list Z)) (r: Z),
  “ (safeExec ATrue (return ((maketuple (l2) (r)))) X_low_level_spec ) ”
  &&  “ (retval = r) ”
  &&  (sll x_pre l2 ))
  -*
  (“ (retval = (list_sum (l1_high_level_spec))) ”
  &&  (sll x_pre l1_high_level_spec )))
.

Definition glibc_slist_clean_iter_back_low_level_spec_entail_low_level_spec_aux :=
forall (B: Type),
forall (x_pre: Z) (cont_low_level_spec_aux: (((@list Z) * Z) -> (@ MonadErr.M  unit B))) (X_low_level_spec_aux: (B -> (unit -> Prop))) (l1_low_level_spec_aux: (@list Z)),
  (“ (range l1_low_level_spec_aux ) ”
  &&  “ (safeExec ATrue (bind ((glibc_slist_clean_iter_back_M (l1_low_level_spec_aux))) (cont_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l1_low_level_spec_aux ))
|--
EX (X_low_level_spec: (((@list Z) * Z) -> (unit -> Prop)))(l1_low_level_spec: (@list Z)),
  (“ (range l1_low_level_spec ) ”
  &&  “ (safeExec ATrue (glibc_slist_clean_iter_back_M (l1_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l1_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l2_2: (@list Z)) (r_2: Z),
  “ (safeExec ATrue (return ((maketuple (l2_2) (r_2)))) X_low_level_spec ) ”
  &&  “ (retval = r_2) ”
  &&  (sll x_pre l2_2 ))
  -*
  (EX (l2: (@list Z)) (r: Z),
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
Axiom proof_of_glibc_slist_clean_iter_back_return_wit_1 : glibc_slist_clean_iter_back_return_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_return_wit_2 : glibc_slist_clean_iter_back_return_wit_2.
Axiom proof_of_glibc_slist_clean_iter_back_partial_solve_wit_1_pure : glibc_slist_clean_iter_back_partial_solve_wit_1_pure.
Axiom proof_of_glibc_slist_clean_iter_back_partial_solve_wit_1 : glibc_slist_clean_iter_back_partial_solve_wit_1.
Axiom proof_of_glibc_slist_clean_iter_back_low_level_spec_entail_high_level_spec : glibc_slist_clean_iter_back_low_level_spec_entail_high_level_spec.
Axiom proof_of_glibc_slist_clean_iter_back_low_level_spec_entail_low_level_spec_aux : glibc_slist_clean_iter_back_low_level_spec_entail_low_level_spec_aux.

End VC_Correct.
