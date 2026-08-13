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
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import safeexec_strategy_proof.

(*----- Function split_while -----*)

Definition split_while_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x: Z) (qv: Z) (pv: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((p_pre) # Ptr  |-> pv)
  **  ((q_pre) # Ptr  |-> qv)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l )
  **  (sll pv l1 )
  **  (sll qv l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_while_safety_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (p_head: Z) (p_next: Z) (qv: Z) (x: Z) (PreH1 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X_low_level_spec )) (PreH2 : (l = (cons (x_data) (l_new)))) (PreH3 : (p_head <> 0)) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((p_pre) # Ptr  |-> p_head)
  **  ((q_pre) # Ptr  |-> qv)
  **  ((&((p_head)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_head)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l1 )
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l_new )
  **  (sll qv l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_while_entail_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec: Z) (pv_low_level_spec: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z))) X_low_level_spec )) ,
  ((p_pre) # Ptr  |-> pv_low_level_spec)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre l_low_level_spec )
  **  (sll pv_low_level_spec (@nil Z) )
  **  (sll qv_low_level_spec (@nil Z) )
|--
  EX (qv: Z)  (pv: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv)
  **  ((q_pre) # Ptr  |-> qv)
  **  (sll x_pre l )
  **  (sll pv l1 )
  **  (sll qv l2 )
.

Definition split_while_entail_wit_2 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x: Z) (qv_2: Z) (pv_2: Z) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (PreH1 : (x <> 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_2) (l1_2) (l2_2)) X_low_level_spec )) ,
  ((p_pre) # Ptr  |-> pv_2)
  **  ((q_pre) # Ptr  |-> qv_2)
  **  (sll x l_2 )
  **  (sll pv_2 l1_2 )
  **  (sll qv_2 l2_2 )
|--
  EX (qv: Z)  (pv: Z)  (x_next: Z)  (x_data: Z)  (l1_new: (@list Z))  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) ” 
  &&  “ (x <> 0) ” 
  &&  “ (l = (cons (x_data) (l1_new))) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  ((p_pre) # Ptr  |-> pv)
  **  ((q_pre) # Ptr  |-> qv)
  **  (sll x_next l1_new )
  **  (sll pv l1 )
  **  (sll qv l2 )
.

Definition split_while_entail_wit_3 := 
(
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x_data_2: Z) (x_next: Z) (pv: Z) (qv_2: Z) (x: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_2) (l1_2) (l2_2)) X_low_level_spec )) (PreH2 : (x <> 0)) (PreH3 : (l_2 = (cons (x_data_2) (l1_new)))) ,
  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> pv)
  **  ((p_pre) # Ptr  |-> x)
  **  ((q_pre) # Ptr  |-> qv_2)
  **  (sll x_next l1_new )
  **  (sll pv l1_2 )
  **  (sll qv_2 l2_2 )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  EX (p_next: Z)  (qv: Z)  (p_head: Z)  (l: (@list Z))  (l_new: (@list Z))  (l2: (@list Z))  (x_data: Z)  (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2) ((cons (x_data) (l1))))) (reversepair)) X_low_level_spec ) ” 
  &&  “ (l = (cons (x_data) (l_new))) ” 
  &&  “ (p_head <> 0) ”
  &&  ((p_pre) # Ptr  |-> p_head)
  **  ((q_pre) # Ptr  |-> qv)
  **  ((&((p_head)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_head)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l1 )
  **  (sll x_next l_new )
  **  (sll qv l2 )
  **  ((( &( "t" ) )) # Ptr  |->_)
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x_data_2: Z) (x: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_2) (l1_2) (l2_2)) X_low_level_spec )) (PreH2 : (x <> 0)) (PreH3 : (l_2 = (cons (x_data_2) (l1_new)))) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2_2) ((cons (x_data_2) (l1_2))))) (reversepair)) X_low_level_spec ) ”
  &&  emp
).

Definition split_while_entail_wit_3_split_goal_1 := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x_data_2: Z) (x: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_2) (l1_2) (l2_2)) X_low_level_spec )) (PreH2 : (x <> 0)) (PreH3 : (l_2 = (cons (x_data_2) (l1_new)))) ,
  (safeExec ATrue (bind ((split_rec_rel (l1_new) (l2_2) ((cons (x_data_2) (l1_2))))) (reversepair)) X_low_level_spec )
.

Definition split_while_entail_wit_4 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data_2: Z) (p_head_2: Z) (p_next: Z) (qv_2: Z) (x: Z) (PreH1 : (x <> 0)) (PreH2 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_2) ((cons (x_data_2) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH3 : (l_2 = (cons (x_data_2) (l_new)))) (PreH4 : (p_head_2 <> 0)) ,
  ((p_pre) # Ptr  |-> p_head_2)
  **  ((q_pre) # Ptr  |-> qv_2)
  **  ((&((p_head_2)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((&((p_head_2)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l1_2 )
  **  (sll x l_new )
  **  (sll qv_2 l2_2 )
|--
  EX (qv: Z)  (p_head: Z)  (x_next: Z)  (x_data2: Z)  (l1_new: (@list Z))  (l: (@list Z))  (l2: (@list Z))  (x_data: Z)  (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((split_rec_rel (l) (l2) ((cons (x_data) (l1))))) (reversepair)) X_low_level_spec ) ” 
  &&  “ (x <> 0) ” 
  &&  “ (l = (cons (x_data2) (l1_new))) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data2)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  ((p_pre) # Ptr  |-> p_head)
  **  ((q_pre) # Ptr  |-> qv)
  **  (sll p_head (cons (x_data) (l1)) )
  **  (sll qv l2 )
  **  (sll x_next l1_new )
.

Definition split_while_entail_wit_5 := 
(
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x_data_2: Z) (x_data2_2: Z) (x_next: Z) (p_head_2: Z) (qv: Z) (x: Z) (PreH1 : (safeExec ATrue (bind ((split_rec_rel (l_2) (l2_2) ((cons (x_data_2) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH2 : (x <> 0)) (PreH3 : (l_2 = (cons (x_data2_2) (l1_new)))) ,
  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data2_2)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> qv)
  **  ((p_pre) # Ptr  |-> p_head_2)
  **  ((q_pre) # Ptr  |-> x)
  **  (sll p_head_2 (cons (x_data_2) (l1_2)) )
  **  (sll qv l2_2 )
  **  (sll x_next l1_new )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
|--
  EX (q_next: Z)  (p_head: Z)  (q_head: Z)  (l: (@list Z))  (l_new: (@list Z))  (x_data: Z)  (l1: (@list Z))  (x_data2: Z)  (l2: (@list Z)) ,
  “ (safeExec ATrue (split_rec_rel (l_new) ((cons (x_data) (l1))) ((cons (x_data2) (l2)))) X_low_level_spec ) ” 
  &&  “ (l = (cons (x_data2) (l_new))) ” 
  &&  “ (q_head <> 0) ”
  &&  ((p_pre) # Ptr  |-> p_head)
  **  ((q_pre) # Ptr  |-> q_head)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x_data2)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_next)
  **  (sll q_next l2 )
  **  (sll p_head (cons (x_data) (l1)) )
  **  (sll x_next l_new )
  **  ((( &( "t" ) )) # Ptr  |->_)
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x_data_2: Z) (x_data2_2: Z) (x: Z) (PreH1 : (safeExec ATrue (bind ((split_rec_rel (l_2) (l2_2) ((cons (x_data_2) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH2 : (x <> 0)) (PreH3 : (l_2 = (cons (x_data2_2) (l1_new)))) ,
  TT && emp 
|--
  “ (safeExec ATrue (split_rec_rel (l1_new) ((cons (x_data_2) (l1_2))) ((cons (x_data2_2) (l2_2)))) X_low_level_spec ) ”
  &&  emp
).

Definition split_while_entail_wit_5_split_goal_1 := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l1_new: (@list Z)) (x_data_2: Z) (x_data2_2: Z) (x: Z) (PreH1 : (safeExec ATrue (bind ((split_rec_rel (l_2) (l2_2) ((cons (x_data_2) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH2 : (x <> 0)) (PreH3 : (l_2 = (cons (x_data2_2) (l1_new)))) ,
  (safeExec ATrue (split_rec_rel (l1_new) ((cons (x_data_2) (l1_2))) ((cons (x_data2_2) (l2_2)))) X_low_level_spec )
.

Definition split_while_entail_wit_6_1 := 
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (x_data2: Z) (p_head: Z) (q_head: Z) (q_next: Z) (x: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_new) ((cons (x_data) (l1_2))) ((cons (x_data2) (l2_2)))) X_low_level_spec )) (PreH2 : (l_2 = (cons (x_data2) (l_new)))) (PreH3 : (q_head <> 0)) ,
  ((p_pre) # Ptr  |-> p_head)
  **  ((q_pre) # Ptr  |-> q_head)
  **  ((&((q_head)  # "list" ->ₛ "data")) # Int  |-> x_data2)
  **  ((&((q_head)  # "list" ->ₛ "next")) # Ptr  |-> q_next)
  **  (sll q_next l2_2 )
  **  (sll p_head (cons (x_data) (l1_2)) )
  **  (sll x l_new )
|--
  EX (qv: Z)  (pv: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv)
  **  ((q_pre) # Ptr  |-> qv)
  **  (sll x l )
  **  (sll pv l1 )
  **  (sll qv l2 )
.

Definition split_while_entail_wit_6_2 := 
(
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (p_head: Z) (p_next: Z) (qv_2: Z) (x: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_2) ((cons (x_data) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH3 : (l_2 = (cons (x_data) (l_new)))) (PreH4 : (p_head <> 0)) ,
  ((p_pre) # Ptr  |-> p_head)
  **  ((q_pre) # Ptr  |-> qv_2)
  **  ((&((p_head)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_head)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (sll p_next l1_2 )
  **  (sll x l_new )
  **  (sll qv_2 l2_2 )
|--
  EX (qv: Z)  (pv: Z)  (l: (@list Z))  (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv)
  **  ((q_pre) # Ptr  |-> qv)
  **  (sll x l )
  **  (sll pv l1 )
  **  (sll qv l2 )
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (p_head: Z) (x: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_2) ((cons (x_data) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH3 : (l_2 = (cons (x_data) (l_new)))) (PreH4 : (p_head <> 0)) ,
  (sll x l_new )
|--
  “ (safeExec ATrue (split_rec_rel ((@nil Z)) ((cons (x_data) (l1_2))) (l2_2)) X_low_level_spec ) ”
  &&  emp
).

Definition split_while_entail_wit_6_2_split_goal_1 := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (p_head: Z) (x: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_2) ((cons (x_data) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH3 : (l_2 = (cons (x_data) (l_new)))) (PreH4 : (p_head <> 0)) ,
  (sll x l_new )
|--
  “ (safeExec ATrue (split_rec_rel ((@nil Z)) ((cons (x_data) (l1_2))) (l2_2)) X_low_level_spec ) ”
.

Definition split_while_entail_wit_6_2_split_goal_spatial := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_2: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (l_new: (@list Z)) (x_data: Z) (p_head: Z) (x: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_2) ((cons (x_data) (l1_2))))) (reversepair)) X_low_level_spec )) (PreH3 : (l_2 = (cons (x_data) (l_new)))) (PreH4 : (p_head <> 0)) ,
  (sll x l_new )
|--
  TT && emp 
.

Definition split_while_return_wit_1 := 
(
forall (q_pre: Z) (p_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x: Z) (qv: Z) (pv: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec )) ,
  ((p_pre) # Ptr  |-> pv)
  **  ((q_pre) # Ptr  |-> qv)
  **  (sll x l )
  **  (sll pv l1 )
  **  (sll qv l2 )
|--
  EX (qv': Z)  (pv': Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv')
  **  ((q_pre) # Ptr  |-> qv')
  **  (sll pv' s1 )
  **  (sll qv' s2 )
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec )) ,
  (sll x l )
|--
  “ (safeExec ATrue (return ((maketuple (l1) (l2)))) X_low_level_spec ) ”
  &&  emp
).

Definition split_while_return_wit_1_split_goal_1 := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec )) ,
  (sll x l )
|--
  “ (safeExec ATrue (return ((maketuple (l1) (l2)))) X_low_level_spec ) ”
.

Definition split_while_return_wit_1_split_goal_spatial := 
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (x: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X_low_level_spec )) ,
  (sll x l )
|--
  TT && emp 
.

Module Type VC_Correct.

Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_split_while_safety_wit_1 : split_while_safety_wit_1.
Axiom proof_of_split_while_safety_wit_2 : split_while_safety_wit_2.
Axiom proof_of_split_while_entail_wit_1 : split_while_entail_wit_1.
Axiom proof_of_split_while_entail_wit_2 : split_while_entail_wit_2.
Axiom proof_of_split_while_entail_wit_3 : split_while_entail_wit_3.
Axiom proof_of_split_while_entail_wit_4 : split_while_entail_wit_4.
Axiom proof_of_split_while_entail_wit_5 : split_while_entail_wit_5.
Axiom proof_of_split_while_entail_wit_6_1 : split_while_entail_wit_6_1.
Axiom proof_of_split_while_entail_wit_6_2 : split_while_entail_wit_6_2.
Axiom proof_of_split_while_return_wit_1 : split_while_return_wit_1.

End VC_Correct.
