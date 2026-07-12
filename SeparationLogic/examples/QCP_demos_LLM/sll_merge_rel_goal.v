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

(*----- Function merge -----*)

Definition merge_safety_wit_1 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) ,
  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition merge_safety_wit_2 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) ,
  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_safety_wit_3 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (x <> 0)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) ,
  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) ,
  ((( &( "ret" ) )) # Ptr  |->_)
  **  (sll x_pre s1 )
  **  (sll y_pre s2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
  **  ((( &( "ret" ) )) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) ( &( "ret" ) ) l3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) ,
  TT && emp 
|--
  “ (safeExec ATrue (merge_from_mid_rel (s1) (s2) ((@nil Z))) X ) ”
  &&  emp
).

Definition merge_entail_wit_1_split_goal_1 := 
forall (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )) ,
  (safeExec ATrue (merge_from_mid_rel (s1) (s2) ((@nil Z))) X )
.

Definition merge_entail_wit_2 := 
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) ,
  (sll x l1_2 )
  **  (sll y l2_2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (ynext: Z)  (xnext: Z)  (ydata: Z)  (l2_new: (@list Z))  (xdata: Z)  (l1_new: (@list Z))  (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ” 
  &&  “ (x <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (l1 = (cons (xdata) (l1_new))) ” 
  &&  “ (l2 = (cons (ydata) (l2_new))) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> xdata)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> ydata)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> xnext)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> ynext)
  **  (sll xnext l1_new )
  **  (sll ynext l2_new )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
.

Definition merge_entail_wit_3_1 := 
(
forall (X: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (l1_new: (@list Z)) (l2_new: (@list Z)) (xdata: Z) (ydata: Z) (xnext: Z) (ynext: Z) (x: Z) (y: Z) (t: Z) (PreH1 : (xdata < ydata)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH3 : (x <> 0)) (PreH4 : (y <> 0)) (PreH5 : (l1_2 = (cons (xdata) (l1_new)))) (PreH6 : (l2_2 = (cons (ydata) (l2_new)))) ,
  ((&((x)  # "list" ->ₛ "data")) # Int  |-> xdata)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> ydata)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> xnext)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> ynext)
  **  (sll xnext l1_new )
  **  (sll ynext l2_new )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll xnext l1 )
  **  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((x)  # "list" ->ₛ "next") l3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (l1_new: (@list Z)) (l2_new: (@list Z)) (xdata: Z) (ydata: Z) (x: Z) (y: Z) (t: Z) (PreH1 : (xdata <= INT_MAX)) (PreH2 : (xdata >= INT_MIN)) (PreH3 : (xdata < ydata)) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH5 : (x <> 0)) (PreH6 : (y <> 0)) (PreH7 : (l1_2 = (cons (xdata) (l1_new)))) (PreH8 : (l2_2 = (cons (ydata) (l2_new)))) ,
  ((&((x)  # "list" ->ₛ "data")) # Int  |-> xdata)
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l3: (@list Z)) ,
  “ (y <> 0) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1_new) ((cons (ydata) (l2_new))) (l3)) X ) ”
  &&  (sllbseg ( &( "ret" ) ) &((x)  # "list" ->ₛ "next") l3 )
).

Definition merge_entail_wit_3_2 := 
(
forall (X: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (l1_new: (@list Z)) (l2_new: (@list Z)) (xdata: Z) (ydata: Z) (xnext: Z) (ynext: Z) (x: Z) (y: Z) (t: Z) (PreH1 : (xdata >= ydata)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH3 : (x <> 0)) (PreH4 : (y <> 0)) (PreH5 : (l1_2 = (cons (xdata) (l1_new)))) (PreH6 : (l2_2 = (cons (ydata) (l2_new)))) ,
  ((&((x)  # "list" ->ₛ "data")) # Int  |-> xdata)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> ydata)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> xnext)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> ynext)
  **  (sll xnext l1_new )
  **  (sll ynext l2_new )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z))  (l3: (@list Z)) ,
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll x l1 )
  **  (sll ynext l2 )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((y)  # "list" ->ₛ "next") l3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (l1_new: (@list Z)) (l2_new: (@list Z)) (xdata: Z) (ydata: Z) (x: Z) (y: Z) (t: Z) (PreH1 : (ydata <= INT_MAX)) (PreH2 : (ydata >= INT_MIN)) (PreH3 : (xdata >= ydata)) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )) (PreH5 : (x <> 0)) (PreH6 : (y <> 0)) (PreH7 : (l1_2 = (cons (xdata) (l1_new)))) (PreH8 : (l2_2 = (cons (ydata) (l2_new)))) ,
  ((&((y)  # "list" ->ₛ "data")) # Int  |-> ydata)
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l3: (@list Z)) ,
  “ (x <> 0) ” 
  &&  “ (safeExec ATrue (merge_from_mid_rel ((cons (xdata) (l1_new))) (l2_new) (l3)) X ) ”
  &&  (sllbseg ( &( "ret" ) ) &((y)  # "list" ->ₛ "next") l3 )
).

Definition merge_entail_wit_4_1 := 
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) ,
  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z)  (s3: (@list Z)) ,
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sll ret s3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) ,
  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z)  (s3: (@list Z)) ,
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sll ret s3 )
).

Definition merge_entail_wit_4_2 := 
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) ,
  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z)  (s3: (@list Z)) ,
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sll ret s3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )) ,
  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z)  (s3: (@list Z)) ,
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sll ret s3 )
).

Definition merge_return_wit_1 := 
forall (X: ((@list Z) -> (unit -> Prop))) (s3_2: (@list Z)) (ret: Z) (PreH1 : (safeExec ATrue (return (s3_2)) X )) ,
  (sll ret s3_2 )
|--
  EX (s3: (@list Z)) ,
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  (sll ret s3 )
.

(*----- Function split_rec -----*)

Definition split_rec_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec: Z) (pv_low_level_spec: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((p_pre) # Ptr  |-> pv_low_level_spec)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre l_low_level_spec )
  **  (sll pv_low_level_spec l1_low_level_spec )
  **  (sll qv_low_level_spec l2_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_rec_entail_wit_1 := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec: Z) (pv_low_level_spec: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  ((p_pre) # Ptr  |-> pv_low_level_spec)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre l_low_level_spec )
  **  (sll pv_low_level_spec l1_low_level_spec )
  **  (sll qv_low_level_spec l2_low_level_spec )
|--
  EX (x_next: Z)  (x_data: Z)  (l_new: (@list Z)) ,
  “ (x_pre <> 0) ” 
  &&  “ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (l_low_level_spec = (cons (x_data) (l_new))) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  ((p_pre) # Ptr  |-> pv_low_level_spec)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_next l_new )
  **  (sll pv_low_level_spec l1_low_level_spec )
  **  (sll qv_low_level_spec l2_low_level_spec )
.

Definition split_rec_entail_wit_2 := 
(
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec: Z) (pv_low_level_spec: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (l_new_2: (@list Z)) (x_data_2: Z) (x_next: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) (PreH3 : (l_low_level_spec = (cons (x_data_2) (l_new_2)))) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data_2)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> pv_low_level_spec)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_next l_new_2 )
  **  (sll pv_low_level_spec l1_low_level_spec )
  **  (sll qv_low_level_spec l2_low_level_spec )
|--
  EX (l_new: (@list Z))  (x_data: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ” 
  &&  “ (l_low_level_spec = (cons (x_data) (l_new))) ”
  &&  ((p_pre) # Ptr  |-> x_pre)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
  **  (sll x_next l_new )
  **  (sll qv_low_level_spec l2_low_level_spec )
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (l_new_2: (@list Z)) (x_data_2: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) (PreH3 : (l_low_level_spec = (cons (x_data_2) (l_new_2)))) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_new_2) (l2_low_level_spec) ((cons (x_data_2) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ”
  &&  emp
).

Definition split_rec_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (l_new_2: (@list Z)) (x_data_2: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) (PreH3 : (l_low_level_spec = (cons (x_data_2) (l_new_2)))) ,
  (safeExec ATrue (bind ((split_rec_rel (l_new_2) (l2_low_level_spec) ((cons (x_data_2) (l1_low_level_spec))))) (reversepair)) X_low_level_spec )
.

Definition split_rec_return_wit_1 := 
(
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec: Z) (pv_low_level_spec: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  ((p_pre) # Ptr  |-> pv_low_level_spec)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre l_low_level_spec )
  **  (sll pv_low_level_spec l1_low_level_spec )
  **  (sll qv_low_level_spec l2_low_level_spec )
|--
  EX (qv': Z)  (pv': Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv')
  **  ((q_pre) # Ptr  |-> qv')
  **  (sll pv' s1 )
  **  (sll qv' s2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple (l1_low_level_spec) (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  emp
).

Definition split_rec_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple (l1_low_level_spec) (l2_low_level_spec)))) X_low_level_spec ) ”
.

Definition split_rec_return_wit_1_split_goal_spatial := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
|--
  TT && emp 
.

Definition split_rec_return_wit_2 := 
(
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (l_new: (@list Z)) (x_data: Z) (qv'_2: Z) (pv'_2: Z) (s1_2: (@list Z)) (s2_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (reversepair) ((maketuple (s1_2) (s2_2)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (l_low_level_spec = (cons (x_data) (l_new)))) ,
  ((q_pre) # Ptr  |-> pv'_2)
  **  ((p_pre) # Ptr  |-> qv'_2)
  **  (sll pv'_2 s1_2 )
  **  (sll qv'_2 s2_2 )
|--
  EX (qv': Z)  (pv': Z)  (s1: (@list Z))  (s2: (@list Z)) ,
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv')
  **  ((q_pre) # Ptr  |-> qv')
  **  (sll pv' s1 )
  **  (sll qv' s2 )
) \/
(
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (l_new: (@list Z)) (x_data: Z) (s1_2: (@list Z)) (s2_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (reversepair) ((maketuple (s1_2) (s2_2)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (l_low_level_spec = (cons (x_data) (l_new)))) ,
  TT && emp 
|--
  “ (safeExec ATrue (return ((maketuple (s2_2) (s1_2)))) X_low_level_spec ) ”
  &&  emp
).

Definition split_rec_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (l_new: (@list Z)) (x_data: Z) (s1_2: (@list Z)) (s2_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (reversepair) ((maketuple (s1_2) (s2_2)))) X_low_level_spec )) (PreH2 : (x_pre <> 0)) (PreH3 : (l_low_level_spec = (cons (x_data) (l_new)))) ,
  (safeExec ATrue (return ((maketuple (s2_2) (s1_2)))) X_low_level_spec )
.

Definition split_rec_partial_solve_wit_1_pure := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (l_new: (@list Z)) (x_data: Z) (t: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec )) (PreH3 : (l_low_level_spec = (cons (x_data) (l_new)))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  (sll t l_new )
  **  (sll qv_low_level_spec l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ”
.

Definition split_rec_partial_solve_wit_1_aux := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec: Z) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (l_new: (@list Z)) (x_data: Z) (t: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec )) (PreH3 : (l_low_level_spec = (cons (x_data) (l_new)))) ,
  ((p_pre) # Ptr  |-> x_pre)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
  **  (sll t l_new )
  **  (sll qv_low_level_spec l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ” 
  &&  “ (l_low_level_spec = (cons (x_data) (l_new))) ”
  &&  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll t l_new )
  **  (sll qv_low_level_spec l2_low_level_spec )
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
.

Definition split_rec_partial_solve_wit_1 := split_rec_partial_solve_wit_1_pure -> split_rec_partial_solve_wit_1_aux.

(*----- Function merge_sort -----*)

Definition merge_sort_safety_wit_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort_safety_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (PreH1 : (p = 0)) (PreH2 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  (sll p (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort_safety_wit_3 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (pv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH2 : (q = 0)) (PreH3 : (p = 0)) (PreH4 : (p = 0)) (PreH5 : (q = 0)) ,
  ((( &( "p" ) )) # Ptr  |-> pv')
  **  ((( &( "q" ) )) # Ptr  |-> qv')
  **  (sll pv' s1 )
  **  (sll qv' s2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort_entail_wit_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ” 
  &&  “ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
.

Definition merge_sort_entail_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (PreH1 : (p = 0)) (PreH2 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll p (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (p = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll p (@nil Z) )
  **  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
.

Definition merge_sort_entail_wit_3 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (p = 0)) (PreH2 : (q = 0)) (PreH3 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (p = 0) ” 
  &&  “ (q = 0) ” 
  &&  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) ”
  &&  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_3_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )
.

Definition merge_sort_entail_wit_4 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (pv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (qv' <> 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH3 : (q = 0)) (PreH4 : (p = 0)) (PreH5 : (p = 0)) (PreH6 : (q = 0)) ,
  (sll pv' s1 )
  **  (sll qv' s2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (qv' <> 0) ” 
  &&  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  (sll pv' l1 )
  **  (sll qv' l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (qv' <> 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH3 : (q = 0)) (PreH4 : (p = 0)) (PreH5 : (p = 0)) (PreH6 : (q = 0)) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((mergesortrec (s1))) ((mergesortrec_loc1 (s2)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_4_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (qv' <> 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH3 : (q = 0)) (PreH4 : (p = 0)) (PreH5 : (p = 0)) (PreH6 : (q = 0)) ,
  (safeExec ATrue (bind ((mergesortrec (s1))) ((mergesortrec_loc1 (s2)))) X_low_level_spec )
.

Definition merge_sort_entail_wit_5 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (q: Z) (l0: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (q <> 0)) ,
  (sll retval l0 )
  **  (sll q l2_2 )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  “ (q <> 0) ” 
  &&  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  (sll retval l1 )
  **  (sll q l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (q: Z) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (q <> 0)) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((mergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_5_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (q: Z) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (q <> 0)) ,
  (safeExec ATrue (bind ((mergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec )
.

Definition merge_sort_entail_wit_6 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (q: Z) (p: Z) (l0: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (q <> 0)) ,
  (sll retval l0 )
  **  (sll p l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  (sll p l1 )
  **  (sll retval l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (q: Z) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (q <> 0)) ,
  TT && emp 
|--
  “ (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_6_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (q: Z) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (q <> 0)) ,
  (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec )
.

Definition merge_sort_return_wit_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s3: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (return (s3)) X_low_level_spec )) ,
  (sll retval s3 )
|--
  EX (l0: (@list Z)) ,
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll retval l0 )
.

Definition merge_sort_return_wit_2 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (pv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (qv' = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH3 : (q = 0)) (PreH4 : (p = 0)) (PreH5 : (p = 0)) (PreH6 : (q = 0)) ,
  (sll pv' s1 )
  **  (sll qv' s2 )
|--
  EX (l0: (@list Z)) ,
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll pv' l0 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (qv' = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH3 : (q = 0)) (PreH4 : (p = 0)) (PreH5 : (p = 0)) (PreH6 : (q = 0)) ,
  (sll qv' s2 )
|--
  “ (safeExec ATrue (return (s1)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_return_wit_2_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (qv' = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH3 : (q = 0)) (PreH4 : (p = 0)) (PreH5 : (p = 0)) (PreH6 : (q = 0)) ,
  (sll qv' s2 )
|--
  “ (safeExec ATrue (return (s1)) X_low_level_spec ) ”
.

Definition merge_sort_return_wit_2_split_goal_spatial := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (p: Z) (q: Z) (qv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (qv' = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH3 : (q = 0)) (PreH4 : (p = 0)) (PreH5 : (p = 0)) (PreH6 : (q = 0)) ,
  (sll qv' s2 )
|--
  TT && emp 
.

Definition merge_sort_partial_solve_wit_1_pure := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (p = 0)) (PreH2 : (q = 0)) (PreH3 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ”
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ”
).

Definition merge_sort_partial_solve_wit_1_pure_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_1_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (p = 0)) (PreH2 : (q = 0)) (PreH3 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )) ,
  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ” 
  &&  “ (q = 0) ” 
  &&  “ (p = 0) ” 
  &&  “ (p = 0) ” 
  &&  “ (q = 0) ” 
  &&  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
  **  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
.

Definition merge_sort_partial_solve_wit_1 := merge_sort_partial_solve_wit_1_pure -> merge_sort_partial_solve_wit_1_aux.

Definition merge_sort_partial_solve_wit_2_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (q: Z) (p: Z) (PreH1 : (q <> 0)) (PreH2 : (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_2_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (q: Z) (p: Z) (PreH1 : (q <> 0)) (PreH2 : (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec )) ,
  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ” 
  &&  “ (q <> 0) ” 
  &&  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  (sll p l1 )
  **  (sll q l2 )
.

Definition merge_sort_partial_solve_wit_2 := merge_sort_partial_solve_wit_2_pure -> merge_sort_partial_solve_wit_2_aux.

Definition merge_sort_partial_solve_wit_3_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (q: Z) (p: Z) (PreH1 : (q <> 0)) (PreH2 : (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_3_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (q: Z) (p: Z) (PreH1 : (q <> 0)) (PreH2 : (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) ,
  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ” 
  &&  “ (q <> 0) ” 
  &&  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  (sll q l2 )
  **  (sll p l1 )
.

Definition merge_sort_partial_solve_wit_3 := merge_sort_partial_solve_wit_3_pure -> merge_sort_partial_solve_wit_3_aux.

Definition merge_sort_partial_solve_wit_4_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll q l2 )
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_4_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) ,
  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  (sll p l1 )
  **  (sll q l2 )
.

Definition merge_sort_partial_solve_wit_4 := merge_sort_partial_solve_wit_4_pure -> merge_sort_partial_solve_wit_4_aux.

(*----- Function merge_sort3 -----*)

Definition merge_sort3_safety_wit_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval = (Zlength (l_low_level_spec)))) (PreH2 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH3 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition merge_sort3_safety_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort3_safety_wit_3 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (PreH1 : (p = 0)) (PreH2 : (8 < (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  (sll p (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort3_entail_wit_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ” 
  &&  “ (8 < (Zlength (l_low_level_spec))) ” 
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_entail_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (PreH1 : (p = 0)) (PreH2 : (8 < (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll p (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (p = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (8 < (Zlength (l_low_level_spec))) ” 
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll p (@nil Z) )
  **  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_entail_wit_3 := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (p = 0)) (PreH2 : (q = 0)) (PreH3 : (8 < (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH5 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (p = 0) ” 
  &&  “ (q = 0) ” 
  &&  “ (8 < (Zlength (l_low_level_spec))) ” 
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) ”
  &&  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (8 < (Zlength (l_low_level_spec)))) (PreH6 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH7 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_3_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (8 < (Zlength (l_low_level_spec)))) (PreH6 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH7 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )
.

Definition merge_sort3_entail_wit_4 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (qv': Z) (pv': Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (gmergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH2 : (q = 0)) (PreH3 : (p = 0)) (PreH4 : (p = 0)) (PreH5 : (q = 0)) (PreH6 : (8 < (Zlength (l_low_level_spec)))) (PreH7 : ((Zlength (l_low_level_spec)) <= INT_MAX)) ,
  (sll pv' s1 )
  **  (sll qv' s2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  (sll pv' l1 )
  **  (sll qv' l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (gmergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH2 : (q = 0)) (PreH3 : (p = 0)) (PreH4 : (p = 0)) (PreH5 : (q = 0)) (PreH6 : (8 < (Zlength (l_low_level_spec)))) (PreH7 : ((Zlength (l_low_level_spec)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((gmergesortrec (s1))) ((gmergesortrec_loc1 (s2)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_4_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (gmergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH2 : (q = 0)) (PreH3 : (p = 0)) (PreH4 : (p = 0)) (PreH5 : (q = 0)) (PreH6 : (8 < (Zlength (l_low_level_spec)))) (PreH7 : ((Zlength (l_low_level_spec)) <= INT_MAX)) ,
  (safeExec ATrue (bind ((gmergesortrec (s1))) ((gmergesortrec_loc1 (s2)))) X_low_level_spec )
.

Definition merge_sort3_entail_wit_5 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (q: Z) (l0: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) ,
  (sll retval l0 )
  **  (sll q l2_2 )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  (sll retval l1 )
  **  (sll q l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_5_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l2_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) ,
  (safeExec ATrue (bind ((gmergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec )
.

Definition merge_sort3_entail_wit_6 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (p: Z) (l0: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) ,
  (sll retval l0 )
  **  (sll p l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  (sll p l1 )
  **  (sll retval l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_6_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) ,
  (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec )
.

Definition merge_sort3_return_wit_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (s3: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (return (s3)) X_low_level_spec )) ,
  (sll retval s3 )
|--
  EX (l0: (@list Z)) ,
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll retval l0 )
.

Definition merge_sort3_return_wit_2 := 
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (l0_2: (@list Z)) (retval: Z) (PreH1 : (Permutation l_low_level_spec l0_2 )) (PreH2 : (incr l0_2 )) (PreH3 : (retval_2 <= 8)) (PreH4 : (retval_2 = (Zlength (l_low_level_spec)))) (PreH5 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH6 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll retval l0_2 )
|--
  EX (l0: (@list Z)) ,
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll retval l0 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (l0_2: (@list Z)) (PreH1 : (Permutation l_low_level_spec l0_2 )) (PreH2 : (incr l0_2 )) (PreH3 : (retval_2 <= 8)) (PreH4 : (retval_2 = (Zlength (l_low_level_spec)))) (PreH5 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH6 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  TT && emp 
|--
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_return_wit_2_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (l0_2: (@list Z)) (PreH1 : (Permutation l_low_level_spec l0_2 )) (PreH2 : (incr l0_2 )) (PreH3 : (retval_2 <= 8)) (PreH4 : (retval_2 = (Zlength (l_low_level_spec)))) (PreH5 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH6 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (safeExec ATrue (return (l0_2)) X_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_1_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (PreH1 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH2 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
.

Definition merge_sort3_partial_solve_wit_1_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (PreH1 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH2 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
|--
  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_1 := merge_sort3_partial_solve_wit_1_pure -> merge_sort3_partial_solve_wit_1_aux.

Definition merge_sort3_partial_solve_wit_2 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval <= 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )) ,
  (sll x_pre l_low_level_spec )
|--
  “ (retval <= 8) ” 
  &&  “ (retval = (Zlength (l_low_level_spec))) ” 
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_3_pure := 
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (p = 0)) (PreH2 : (q = 0)) (PreH3 : (8 < (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH5 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ”
) \/
(
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (8 < (Zlength (l_low_level_spec)))) (PreH6 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH7 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ”
).

Definition merge_sort3_partial_solve_wit_3_pure_split_goal_1 := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (q = 0)) (PreH2 : (p = 0)) (PreH3 : (p = 0)) (PreH4 : (q = 0)) (PreH5 : (8 < (Zlength (l_low_level_spec)))) (PreH6 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH7 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_3_aux := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (p: Z) (q: Z) (PreH1 : (p = 0)) (PreH2 : (q = 0)) (PreH3 : (8 < (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH5 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) ,
  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ” 
  &&  “ (q = 0) ” 
  &&  “ (p = 0) ” 
  &&  “ (p = 0) ” 
  &&  “ (q = 0) ” 
  &&  “ (8 < (Zlength (l_low_level_spec))) ” 
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
  **  (sll p (@nil Z) )
  **  (sll q (@nil Z) )
.

Definition merge_sort3_partial_solve_wit_3 := merge_sort3_partial_solve_wit_3_pure -> merge_sort3_partial_solve_wit_3_aux.

Definition merge_sort3_partial_solve_wit_4_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_4_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec )) ,
  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  (sll p l1 )
  **  (sll q l2 )
.

Definition merge_sort3_partial_solve_wit_4 := merge_sort3_partial_solve_wit_4_pure -> merge_sort3_partial_solve_wit_4_aux.

Definition merge_sort3_partial_solve_wit_5_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_5_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) ,
  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  (sll q l2 )
  **  (sll p l1 )
.

Definition merge_sort3_partial_solve_wit_5 := merge_sort3_partial_solve_wit_5_pure -> merge_sort3_partial_solve_wit_5_aux.

Definition merge_sort3_partial_solve_wit_6_pure := 
forall (x_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (sll p l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (sll q l2 )
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_6_aux := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l1: (@list Z)) (l2: (@list Z)) (p: Z) (q: Z) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) ,
  (sll p l1 )
  **  (sll q l2 )
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ” 
  &&  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  (sll p l1 )
  **  (sll q l2 )
.

Definition merge_sort3_partial_solve_wit_6 := merge_sort3_partial_solve_wit_6_pure -> merge_sort3_partial_solve_wit_6_aux.

Definition merge_sort3_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Z) -> (@ StateRelMonad.M  unit B))) (l_low_level_spec_aux: (@list Z)) ,
  “ ((Zlength (l_low_level_spec_aux)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort3_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l_high_level_spec: (@list Z)) ,
  “ ((Zlength (l_high_level_spec)) <= INT_MAX) ”
  &&  (sll x_pre l_high_level_spec )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ ((Zlength (l_low_level_spec)) <= INT_MAX) ” 
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  “ (Permutation l_high_level_spec l0 ) ” 
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort2_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Z) -> (@ StateRelMonad.M  unit B))) (l_low_level_spec_aux: (@list Z)) ,
  “ (safeExec ATrue (bind ((gmergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort2_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l_high_level_spec: (@list Z)) ,
  (sll x_pre l_high_level_spec )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  “ (Permutation l_high_level_spec l0 ) ” 
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (x_pre: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: ((@list Z) -> (@ StateRelMonad.M  unit B))) (l_low_level_spec_aux: (@list Z)) ,
  “ (safeExec ATrue (bind ((mergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l_high_level_spec: (@list Z)) ,
  (sll x_pre l_high_level_spec )
|--
EX (l_low_level_spec: (@list Z)) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  ((EX l0_2 retval_2,
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval_2 l0_2 ))
  -*
  (EX l0 retval,
  “ (Permutation l_high_level_spec l0 ) ” 
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
.

Definition split_rec_derive_low_level_spec_aux_by_low_level_spec := 
forall (B: Type) ,
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_low_level_spec_aux: Z) (pv_low_level_spec_aux: Z) (X_low_level_spec_aux: (B -> (unit -> Prop))) (c_low_level_spec_aux: (((@list Z) * (@list Z)) -> (@ StateRelMonad.M  unit B))) (l2_low_level_spec_aux: (@list Z)) (l1_low_level_spec_aux: (@list Z)) (l_low_level_spec_aux: (@list Z)) ,
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec_aux) (l1_low_level_spec_aux) (l2_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  ((p_pre) # Ptr  |-> pv_low_level_spec_aux)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec_aux)
  **  (sll x_pre l_low_level_spec_aux )
  **  (sll pv_low_level_spec_aux l1_low_level_spec_aux )
  **  (sll qv_low_level_spec_aux l2_low_level_spec_aux )
|--
EX (l_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (pv_low_level_spec: Z) (qv_low_level_spec: Z) ,
  (“ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv_low_level_spec)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre l_low_level_spec )
  **  (sll pv_low_level_spec l1_low_level_spec )
  **  (sll qv_low_level_spec l2_low_level_spec ))
  **
  ((EX qv'_2 pv'_2 s1_2 s2_2,
  “ (safeExec ATrue (return ((maketuple (s1_2) (s2_2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv'_2)
  **  ((q_pre) # Ptr  |-> qv'_2)
  **  (sll pv'_2 s1_2 )
  **  (sll qv'_2 s2_2 ))
  -*
  (EX qv' pv' s1 s2,
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) ((maketuple (s1) (s2)))) X_low_level_spec_aux ) ”
  &&  ((p_pre) # Ptr  |-> pv')
  **  ((q_pre) # Ptr  |-> qv')
  **  (sll pv' s1 )
  **  (sll qv' s2 )))
.

Definition split_rec_derive_high_level_spec_by_low_level_spec := 
forall (q_pre: Z) (p_pre: Z) (x_pre: Z) (qv_high_level_spec: Z) (pv_high_level_spec: Z) (X_high_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_high_level_spec: (@list Z)) ,
  “ (safeExec ATrue (split_rel (l_high_level_spec)) X_high_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv_high_level_spec)
  **  ((q_pre) # Ptr  |-> qv_high_level_spec)
  **  (sll x_pre l_high_level_spec )
  **  (sll pv_high_level_spec nil )
  **  (sll qv_high_level_spec nil )
|--
EX (l_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l2_low_level_spec: (@list Z)) (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (pv_low_level_spec: Z) (qv_low_level_spec: Z) ,
  (“ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv_low_level_spec)
  **  ((q_pre) # Ptr  |-> qv_low_level_spec)
  **  (sll x_pre l_low_level_spec )
  **  (sll pv_low_level_spec l1_low_level_spec )
  **  (sll qv_low_level_spec l2_low_level_spec ))
  **
  ((EX qv'_2 pv'_2 s1_2 s2_2,
  “ (safeExec ATrue (return ((maketuple (s1_2) (s2_2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv'_2)
  **  ((q_pre) # Ptr  |-> qv'_2)
  **  (sll pv'_2 s1_2 )
  **  (sll qv'_2 s2_2 ))
  -*
  (EX qv' pv' s1 s2,
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X_high_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> pv')
  **  ((q_pre) # Ptr  |-> qv')
  **  (sll pv' s1 )
  **  (sll qv' s2 )))
.

Module Type VC_Correct.

Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Axiom proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Axiom proof_of_merge_safety_wit_3 : merge_safety_wit_3.
Axiom proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Axiom proof_of_merge_entail_wit_2 : merge_entail_wit_2.
Axiom proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Axiom proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Axiom proof_of_merge_entail_wit_4_1 : merge_entail_wit_4_1.
Axiom proof_of_merge_entail_wit_4_2 : merge_entail_wit_4_2.
Axiom proof_of_merge_return_wit_1 : merge_return_wit_1.
Axiom proof_of_split_rec_safety_wit_1 : split_rec_safety_wit_1.
Axiom proof_of_split_rec_entail_wit_1 : split_rec_entail_wit_1.
Axiom proof_of_split_rec_entail_wit_2 : split_rec_entail_wit_2.
Axiom proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Axiom proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Axiom proof_of_split_rec_partial_solve_wit_1_pure : split_rec_partial_solve_wit_1_pure.
Axiom proof_of_split_rec_partial_solve_wit_1 : split_rec_partial_solve_wit_1.
Axiom proof_of_merge_sort_safety_wit_1 : merge_sort_safety_wit_1.
Axiom proof_of_merge_sort_safety_wit_2 : merge_sort_safety_wit_2.
Axiom proof_of_merge_sort_safety_wit_3 : merge_sort_safety_wit_3.
Axiom proof_of_merge_sort_entail_wit_1 : merge_sort_entail_wit_1.
Axiom proof_of_merge_sort_entail_wit_2 : merge_sort_entail_wit_2.
Axiom proof_of_merge_sort_entail_wit_3 : merge_sort_entail_wit_3.
Axiom proof_of_merge_sort_entail_wit_4 : merge_sort_entail_wit_4.
Axiom proof_of_merge_sort_entail_wit_5 : merge_sort_entail_wit_5.
Axiom proof_of_merge_sort_entail_wit_6 : merge_sort_entail_wit_6.
Axiom proof_of_merge_sort_return_wit_1 : merge_sort_return_wit_1.
Axiom proof_of_merge_sort_return_wit_2 : merge_sort_return_wit_2.
Axiom proof_of_merge_sort_partial_solve_wit_1_pure : merge_sort_partial_solve_wit_1_pure.
Axiom proof_of_merge_sort_partial_solve_wit_1 : merge_sort_partial_solve_wit_1.
Axiom proof_of_merge_sort_partial_solve_wit_2_pure : merge_sort_partial_solve_wit_2_pure.
Axiom proof_of_merge_sort_partial_solve_wit_2 : merge_sort_partial_solve_wit_2.
Axiom proof_of_merge_sort_partial_solve_wit_3_pure : merge_sort_partial_solve_wit_3_pure.
Axiom proof_of_merge_sort_partial_solve_wit_3 : merge_sort_partial_solve_wit_3.
Axiom proof_of_merge_sort_partial_solve_wit_4_pure : merge_sort_partial_solve_wit_4_pure.
Axiom proof_of_merge_sort_partial_solve_wit_4 : merge_sort_partial_solve_wit_4.
Axiom proof_of_merge_sort3_safety_wit_1 : merge_sort3_safety_wit_1.
Axiom proof_of_merge_sort3_safety_wit_2 : merge_sort3_safety_wit_2.
Axiom proof_of_merge_sort3_safety_wit_3 : merge_sort3_safety_wit_3.
Axiom proof_of_merge_sort3_entail_wit_1 : merge_sort3_entail_wit_1.
Axiom proof_of_merge_sort3_entail_wit_2 : merge_sort3_entail_wit_2.
Axiom proof_of_merge_sort3_entail_wit_3 : merge_sort3_entail_wit_3.
Axiom proof_of_merge_sort3_entail_wit_4 : merge_sort3_entail_wit_4.
Axiom proof_of_merge_sort3_entail_wit_5 : merge_sort3_entail_wit_5.
Axiom proof_of_merge_sort3_entail_wit_6 : merge_sort3_entail_wit_6.
Axiom proof_of_merge_sort3_return_wit_1 : merge_sort3_return_wit_1.
Axiom proof_of_merge_sort3_return_wit_2 : merge_sort3_return_wit_2.
Axiom proof_of_merge_sort3_partial_solve_wit_1_pure : merge_sort3_partial_solve_wit_1_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_1 : merge_sort3_partial_solve_wit_1.
Axiom proof_of_merge_sort3_partial_solve_wit_2 : merge_sort3_partial_solve_wit_2.
Axiom proof_of_merge_sort3_partial_solve_wit_3_pure : merge_sort3_partial_solve_wit_3_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_3 : merge_sort3_partial_solve_wit_3.
Axiom proof_of_merge_sort3_partial_solve_wit_4_pure : merge_sort3_partial_solve_wit_4_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_4 : merge_sort3_partial_solve_wit_4.
Axiom proof_of_merge_sort3_partial_solve_wit_5_pure : merge_sort3_partial_solve_wit_5_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_5 : merge_sort3_partial_solve_wit_5.
Axiom proof_of_merge_sort3_partial_solve_wit_6_pure : merge_sort3_partial_solve_wit_6_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_6 : merge_sort3_partial_solve_wit_6.
Axiom proof_of_merge_sort3_derive_low_level_spec_aux_by_low_level_spec : merge_sort3_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_merge_sort3_derive_high_level_spec_by_low_level_spec : merge_sort3_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_merge_sort2_derive_low_level_spec_aux_by_low_level_spec : merge_sort2_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_merge_sort2_derive_high_level_spec_by_low_level_spec : merge_sort2_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_merge_sort_derive_low_level_spec_aux_by_low_level_spec : merge_sort_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_split_rec_derive_low_level_spec_aux_by_low_level_spec : split_rec_derive_low_level_spec_aux_by_low_level_spec.
Axiom proof_of_split_rec_derive_high_level_spec_by_low_level_spec : split_rec_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
