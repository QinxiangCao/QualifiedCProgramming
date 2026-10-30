From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.sll_lib.
From SimpleC.Verification Require Import SafeExecPrelude.
Require Import SimpleC.EE.QCP_demos_human.sll_merge_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_strategy_proof.
From SimpleC.Verification Require Import safeexec_strategy_goal.
From SimpleC.Verification Require Import safeexec_strategy_proof.

(*----- Function merge -----*)

Definition merge_safety_wit_1 :=
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
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
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
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
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (x <> 0)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
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
forall (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (x_pre: Z) (y_pre: Z) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )),
  ((( &( "ret" ) )) # Ptr  |->_)
  **  (sll x_pre s1 )
  **  (sll y_pre s2 )
|--
  EX (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)),
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll x_pre l1 )
  **  (sll y_pre l2 )
  **  ((( &( "ret" ) )) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) ( &( "ret" ) ) l3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )),
  TT && emp 
|--
  “ (safeExec ATrue (merge_from_mid_rel (s1) (s2) ((@nil Z))) X ) ”
  &&  emp
).

Definition merge_entail_wit_1_split_goal_1 :=
forall (X: ((@list Z) -> (unit -> Prop))) (s2: (@list Z)) (s1: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (s1) (s2)) X )),
  (safeExec ATrue (merge_from_mid_rel (s1) (s2) ((@nil Z))) X )
.

Definition merge_entail_wit_2_1 :=
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y_next: Z) (y_data: Z) (l2_new: (@list Z)) (PreH1 : (x_data < y_data)) (PreH2 : (l2_2 = (cons (y_data) (l2_new)))) (PreH3 : (l1_2 = (cons (x_data) (l1_new)))) (PreH4 : (y <> 0)) (PreH5 : (x <> 0)) (PreH6 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )),
  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)),
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll x_next l1 )
  **  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((x)  # "list" ->ₛ "next") l3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_data: Z) (l1_new: (@list Z)) (y_data: Z) (l2_new: (@list Z)) (PreH1 : (x_data <= INT_MAX)) (PreH2 : (x_data >= INT_MIN)) (PreH3 : (x_data < y_data)) (PreH4 : (l2_2 = (cons (y_data) (l2_new)))) (PreH5 : (l1_2 = (cons (x_data) (l1_new)))) (PreH6 : (y <> 0)) (PreH7 : (x <> 0)) (PreH8 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )),
  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l3: (@list Z)),
  “ (y <> 0) ”
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1_new) ((cons (y_data) (l2_new))) (l3)) X ) ”
  &&  (sllbseg ( &( "ret" ) ) &((x)  # "list" ->ₛ "next") l3 )
).

Definition merge_entail_wit_2_2 :=
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (y_next: Z) (y_data: Z) (l2_new: (@list Z)) (PreH1 : (x_data >= y_data)) (PreH2 : (l2_2 = (cons (y_data) (l2_new)))) (PreH3 : (l1_2 = (cons (x_data) (l1_new)))) (PreH4 : (y <> 0)) (PreH5 : (x <> 0)) (PreH6 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )),
  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)),
  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll x l1 )
  **  (sll y_next l2 )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) &((y)  # "list" ->ₛ "next") l3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (l3_2: (@list Z)) (x_data: Z) (l1_new: (@list Z)) (y_data: Z) (l2_new: (@list Z)) (PreH1 : (y_data <= INT_MAX)) (PreH2 : (y_data >= INT_MIN)) (PreH3 : (x_data >= y_data)) (PreH4 : (l2_2 = (cons (y_data) (l2_new)))) (PreH5 : (l1_2 = (cons (x_data) (l1_new)))) (PreH6 : (y <> 0)) (PreH7 : (x <> 0)) (PreH8 : (safeExec ATrue (merge_from_mid_rel (l1_2) (l2_2) (l3_2)) X )),
  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3_2 )
|--
  EX (l3: (@list Z)),
  “ (x <> 0) ”
  &&  “ (safeExec ATrue (merge_from_mid_rel ((cons (x_data) (l1_new))) (l2_new) (l3)) X ) ”
  &&  (sllbseg ( &( "ret" ) ) &((y)  # "list" ->ₛ "next") l3 )
).

Definition merge_return_wit_1 :=
(
forall (X: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  (sllseg ret y l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)),
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  (sll ret s3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  (sllseg ret y l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)),
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  (sll ret s3 )
).

Definition merge_return_wit_2 :=
(
forall (X: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) (PreH1 : (y = 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  (sllseg ret x l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)),
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  (sll ret s3 )
) \/
(
forall (X: ((@list Z) -> (unit -> Prop))) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (ret: Z) (PreH1 : (y = 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  (sllseg ret x l3 )
  **  (sll x l1 )
  **  (sll y l2 )
|--
  EX (s3: (@list Z)),
  “ (safeExec ATrue (return (s3)) X ) ”
  &&  (sll ret s3 )
).

Definition merge_partial_solve_wit_1_pure :=
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  ((( &( "x" ) )) # Ptr  |-> x)
  **  (sll x l1 )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (x <> 0) ”
.

Definition merge_partial_solve_wit_1_aux :=
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (y <> 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (x <> 0) ”
  &&  “ (y <> 0) ”
  &&  “ (x <> 0) ”
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
.

Definition merge_partial_solve_wit_1 := merge_partial_solve_wit_1_pure -> merge_partial_solve_wit_1_aux.

Definition merge_partial_solve_wit_2_pure :=
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (PreH1 : (l1 = (cons (x_data) (l1_new)))) (PreH2 : (y <> 0)) (PreH3 : (x <> 0)) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (sll y l2 )
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (y <> 0) ”
.

Definition merge_partial_solve_wit_2_aux :=
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (x_next: Z) (x_data: Z) (l1_new: (@list Z)) (PreH1 : (l1 = (cons (x_data) (l1_new)))) (PreH2 : (y <> 0)) (PreH3 : (x <> 0)) (PreH4 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  (sll y l2 )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (y <> 0) ”
  &&  “ (l1 = (cons (x_data) (l1_new))) ”
  &&  “ (y <> 0) ”
  &&  “ (x <> 0) ”
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  (sll y l2 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
  **  ((t) # Ptr  |->_)
  **  (sllbseg ( &( "ret" ) ) t l3 )
.

Definition merge_partial_solve_wit_2 := merge_partial_solve_wit_2_pure -> merge_partial_solve_wit_2_aux.

Definition merge_partial_solve_wit_3 :=
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (y = 0)) (PreH2 : (x <> 0)) (PreH3 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (y = 0) ”
  &&  “ (x <> 0) ”
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  ((t) # Ptr  |-> x)
  **  (sllbseg ( &( "ret" ) ) t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_partial_solve_wit_4 :=
forall (X: ((@list Z) -> (unit -> Prop))) (t: Z) (y: Z) (x: Z) (l1: (@list Z)) (l2: (@list Z)) (l3: (@list Z)) (PreH1 : (x = 0)) (PreH2 : (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X )),
  (sll x l1 )
  **  (sll y l2 )
  **  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  “ (x = 0) ”
  &&  “ (safeExec ATrue (merge_from_mid_rel (l1) (l2) (l3)) X ) ”
  &&  ((t) # Ptr  |-> y)
  **  (sllbseg ( &( "ret" ) ) t l3 )
  **  (sll x l1 )
  **  (sll y l2 )
.

Definition merge_which_implies_wit_1 :=
forall (l1: (@list Z)) (x: Z) (PreH1 : (x <> 0)),
  (sll x l1 )
|--
  EX (x_next: Z) (x_data: Z) (l1_new: (@list Z)),
  “ (l1 = (cons (x_data) (l1_new))) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l1_new )
.

Definition merge_which_implies_wit_2 :=
forall (l2: (@list Z)) (y: Z) (PreH1 : (y <> 0)),
  (sll y l2 )
|--
  EX (y_next: Z) (y_data: Z) (l2_new: (@list Z)),
  “ (l2 = (cons (y_data) (l2_new))) ”
  &&  ((&((y)  # "list" ->ₛ "data")) # Int  |-> y_data)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_next)
  **  (sll y_next l2_new )
.

Definition merge_which_implies_wit_3 :=
(
forall (u: Z) (l3: (@list Z)) (t: Z),
  ((t) # Ptr  |-> u)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z),
  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sllseg ret u l3 )
) \/
(
forall (u: Z) (l3: (@list Z)) (t: Z),
  ((t) # Ptr  |-> u)
  **  (sllbseg ( &( "ret" ) ) t l3 )
|--
  EX (ret: Z),
  ((( &( "ret" ) )) # Ptr  |-> ret)
  **  (sllseg ret u l3 )
).

(*----- Function split_rec -----*)

Definition split_rec_safety_wit_1 :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (p_v: Z) (q_v: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition split_rec_return_wit_1 :=
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (p_v_2: Z) (q_v_2: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 l2_low_level_spec )
|--
  EX (q_v: Z) (p_v: Z) (s1: (@list Z)) (s2: (@list Z)),
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v s1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v s2 )
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple (l1_low_level_spec) (l2_low_level_spec)))) X_low_level_spec ) ”
  &&  emp
).

Definition split_rec_return_wit_1_split_goal_1 :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (return ((maketuple (l1_low_level_spec) (l2_low_level_spec)))) X_low_level_spec ) ”
.

Definition split_rec_return_wit_1_split_goal_spatial :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (x_pre = 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  TT && emp 
.

Definition split_rec_return_wit_2 :=
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (x_data: Z) (l_new: (@list Z)) (q_v_2: Z) (p_v_2: Z) (s1_2: (@list Z)) (s2_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (reversepair) ((maketuple (s1_2) (s2_2)))) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (x_pre <> 0)),
  ((q_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 s1_2 )
  **  ((p_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 s2_2 )
|--
  EX (q_v: Z) (p_v: Z) (s1: (@list Z)) (s2: (@list Z)),
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v s1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v s2 )
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (x_data: Z) (l_new: (@list Z)) (s1_2: (@list Z)) (s2_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (reversepair) ((maketuple (s1_2) (s2_2)))) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (x_pre <> 0)),
  TT && emp 
|--
  “ (safeExec ATrue (return ((maketuple (s2_2) (s1_2)))) X_low_level_spec ) ”
  &&  emp
).

Definition split_rec_return_wit_2_split_goal_1 :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (x_data: Z) (l_new: (@list Z)) (s1_2: (@list Z)) (s2_2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (reversepair) ((maketuple (s1_2) (s2_2)))) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (x_pre <> 0)),
  (safeExec ATrue (return ((maketuple (s2_2) (s1_2)))) X_low_level_spec )
.

Definition split_rec_partial_solve_wit_1_pure :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (p_v: Z) (q_v: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
|--
  “ (x_pre <> 0) ”
.

Definition split_rec_partial_solve_wit_1_aux :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (p_v: Z) (q_v: Z) (PreH1 : (x_pre <> 0)) (PreH2 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
|--
  “ (x_pre <> 0) ”
  &&  “ (x_pre <> 0) ”
  &&  “ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
.

Definition split_rec_partial_solve_wit_1 := split_rec_partial_solve_wit_1_pure -> split_rec_partial_solve_wit_1_aux.

Definition split_rec_partial_solve_wit_2_pure :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (p_v: Z) (q_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) (PreH1 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH2 : (x_pre <> 0)) (PreH3 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  ((( &( "t" ) )) # Ptr  |-> x_next)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_v)
  **  (sll x_next l_new )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll p_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
|--
  “ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  “ (l_low_level_spec = (cons (x_data) (l_new))) ”
  &&  “ (x_pre <> 0) ”
.

Definition split_rec_partial_solve_wit_2_aux :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (p_v: Z) (q_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) (PreH1 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH2 : (x_pre <> 0)) (PreH3 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )),
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_v)
  **  (sll x_next l_new )
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll p_v l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
|--
  “ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  “ (l_low_level_spec = (cons (x_data) (l_new))) ”
  &&  “ (x_pre <> 0) ”
  &&  “ (l_low_level_spec = (cons (x_data) (l_new))) ”
  &&  “ (x_pre <> 0) ”
  &&  “ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_v)
  **  (sll p_v l1_low_level_spec )
  **  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
.

Definition split_rec_partial_solve_wit_2 := split_rec_partial_solve_wit_2_pure -> split_rec_partial_solve_wit_2_aux.

Definition split_rec_partial_solve_wit_3_pure :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (q_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) (PreH1 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (x_pre <> 0)),
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
  **  ((( &( "t" ) )) # Ptr  |-> x_next)
  **  (sll x_next l_new )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ”
.

Definition split_rec_partial_solve_wit_3_aux :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_pre: Z) (p_pre: Z) (q_pre: Z) (q_v: Z) (x_next: Z) (x_data: Z) (l_new: (@list Z)) (PreH1 : (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (x_pre <> 0)),
  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
  **  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ”
  &&  “ (l_low_level_spec = (cons (x_data) (l_new))) ”
  &&  “ (x_pre <> 0) ”
  &&  (sll x_next l_new )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec )
  **  ((p_pre) # Ptr  |-> x_pre)
  **  (sll x_pre (cons (x_data) (l1_low_level_spec)) )
.

Definition split_rec_partial_solve_wit_3 := split_rec_partial_solve_wit_3_pure -> split_rec_partial_solve_wit_3_aux.

Definition split_rec_which_implies_wit_1 :=
forall (l: (@list Z)) (x: Z) (PreH1 : (x <> 0)),
  (sll x l )
|--
  EX (x_next: Z) (x_data: Z) (l_new: (@list Z)),
  “ (l = (cons (x_data) (l_new))) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> x_next)
  **  (sll x_next l_new )
.

Definition split_rec_which_implies_wit_2 :=
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_data: Z) (l_new: (@list Z)) (p: Z) (p_v: Z) (p_v_next: Z) (t: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (p_v <> 0)),
  ((p) # Ptr  |-> p_v)
  **  ((&((p_v)  # "list" ->ₛ "data")) # Int  |-> x_data)
  **  ((&((p_v)  # "list" ->ₛ "next")) # Ptr  |-> p_v_next)
  **  (sll p_v_next l1_low_level_spec )
  **  (sll t l_new )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ”
  &&  ((p) # Ptr  |-> p_v)
  **  (sll p_v (cons (x_data) (l1_low_level_spec)) )
  **  (sll t l_new )
) \/
(
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_data: Z) (l_new: (@list Z)) (p_v: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (p_v <> 0)),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec ) ”
  &&  emp
).

Definition split_rec_which_implies_wit_2_split_goal_1 :=
forall (X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))) (l2_low_level_spec: (@list Z)) (l1_low_level_spec: (@list Z)) (l_low_level_spec: (@list Z)) (x_data: Z) (l_new: (@list Z)) (p_v: Z) (PreH1 : (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec )) (PreH2 : (l_low_level_spec = (cons (x_data) (l_new)))) (PreH3 : (p_v <> 0)),
  (safeExec ATrue (bind ((split_rec_rel (l_new) (l2_low_level_spec) ((cons (x_data) (l1_low_level_spec))))) (reversepair)) X_low_level_spec )
.

(*----- Function merge_sort -----*)

Definition merge_sort_safety_wit_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort_safety_wit_2 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 (@nil Z) )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort_safety_wit_3 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (q_v: Z) (p_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  ((( &( "p" ) )) # Ptr  |-> p_v)
  **  (sll p_v s1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_v)
  **  (sll q_v s2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort_entail_wit_1 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_1_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )
.

Definition merge_sort_entail_wit_2 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (p_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (q_v <> 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  (sll p_v s1 )
  **  (sll q_v s2 )
|--
  EX (l1: (@list Z)) (l2: (@list Z)),
  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  “ (q_v <> 0) ”
  &&  (sll p_v l1 )
  **  (sll q_v l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (q_v <> 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((mergesortrec (s1))) ((mergesortrec_loc1 (s2)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_2_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (q_v <> 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  (safeExec ATrue (bind ((mergesortrec (s1))) ((mergesortrec_loc1 (s2)))) X_low_level_spec )
.

Definition merge_sort_entail_wit_3 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (l2_2: (@list Z)) (l0: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (sll retval l0 )
  **  (sll q_v l2_2 )
|--
  EX (l2: (@list Z)) (l1: (@list Z)),
  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  “ (q_v <> 0) ”
  &&  (sll retval l1 )
  **  (sll q_v l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (l2_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((mergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_3_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (l2_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (safeExec ATrue (bind ((mergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec )
.

Definition merge_sort_entail_wit_4 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (retval: Z) (l1_2: (@list Z)) (l0: (@list Z)) (retval_2: Z) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (sll retval_2 l0 )
  **  (sll retval l1_2 )
|--
  EX (l1: (@list Z)) (l2: (@list Z)),
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  “ (q_v <> 0) ”
  &&  (sll retval l1 )
  **  (sll retval_2 l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (l1_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  TT && emp 
|--
  “ (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_entail_wit_4_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (l1_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec )
.

Definition merge_sort_return_wit_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (s3: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (return (s3)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (sll retval s3 )
|--
  EX (l0: (@list Z)),
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll retval l0 )
.

Definition merge_sort_return_wit_2 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (p_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (q_v = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  (sll p_v s1 )
  **  (sll q_v s2 )
|--
  EX (l0: (@list Z)),
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll p_v l0 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (q_v = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  (sll q_v s2 )
|--
  “ (safeExec ATrue (return (s1)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort_return_wit_2_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (q_v = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  (sll q_v s2 )
|--
  “ (safeExec ATrue (return (s1)) X_low_level_spec ) ”
.

Definition merge_sort_return_wit_2_split_goal_spatial :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (q_v = 0)) (PreH2 : (safeExec ATrue (applyf (mergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )),
  (sll q_v s2 )
|--
  TT && emp 
.

Definition merge_sort_partial_solve_wit_1_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ”
.

Definition merge_sort_partial_solve_wit_1_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ”
  &&  “ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort_partial_solve_wit_1 := merge_sort_partial_solve_wit_1_pure -> merge_sort_partial_solve_wit_1_aux.

Definition merge_sort_partial_solve_wit_2_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 (@nil Z) )
  **  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ”
.

Definition merge_sort_partial_solve_wit_2_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ”
  &&  “ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort_partial_solve_wit_2 := merge_sort_partial_solve_wit_2_pure -> merge_sort_partial_solve_wit_2_aux.

Definition merge_sort_partial_solve_wit_3_pure :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )),
  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ”
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )),
  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ”
).

Definition merge_sort_partial_solve_wit_3_pure_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )),
  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_3_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (mergesortrec_loc0)) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (mergesortrec_loc0)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
  **  (sll 0 (@nil Z) )
  **  (sll 0 (@nil Z) )
.

Definition merge_sort_partial_solve_wit_3 := merge_sort_partial_solve_wit_3_pure -> merge_sort_partial_solve_wit_3_aux.

Definition merge_sort_partial_solve_wit_4_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (q_v: Z) (p_v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  ((( &( "p" ) )) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_4_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (p_v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (sll p_v l1 )
  **  (sll q_v l2 )
|--
  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((mergesortrec (l1))) ((mergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  “ (q_v <> 0) ”
  &&  (sll p_v l1 )
  **  (sll q_v l2 )
.

Definition merge_sort_partial_solve_wit_4 := merge_sort_partial_solve_wit_4_pure -> merge_sort_partial_solve_wit_4_aux.

Definition merge_sort_partial_solve_wit_5_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (q_v: Z) (retval: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (sll retval l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_5_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (retval: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (sll retval l1 )
  **  (sll q_v l2 )
|--
  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((mergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  “ (q_v <> 0) ”
  &&  (sll q_v l2 )
  **  (sll retval l1 )
.

Definition merge_sort_partial_solve_wit_5 := merge_sort_partial_solve_wit_5_pure -> merge_sort_partial_solve_wit_5_aux.

Definition merge_sort_partial_solve_wit_6_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (x_pre: Z) (q_v: Z) (retval: Z) (retval_2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (sll retval l1 )
  **  ((( &( "q" ) )) # Ptr  |-> retval_2)
  **  (sll retval_2 l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
.

Definition merge_sort_partial_solve_wit_6_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (q_v: Z) (retval: Z) (retval_2: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) (PreH2 : (q_v <> 0)),
  (sll retval l1 )
  **  (sll retval_2 l2 )
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  “ (q_v <> 0) ”
  &&  (sll retval l1 )
  **  (sll retval_2 l2 )
.

Definition merge_sort_partial_solve_wit_6 := merge_sort_partial_solve_wit_6_pure -> merge_sort_partial_solve_wit_6_aux.

Definition merge_sort_which_implies_wit_1 :=
forall (p: Z) (PreH1 : (p = 0)),
  TT && emp 
|--
  (sll p (@nil Z) )
.

Definition merge_sort_which_implies_wit_2 :=
forall (q: Z) (PreH1 : (q = 0)),
  TT && emp 
|--
  (sll q (@nil Z) )
.

(*----- Function merge_sort3 -----*)

Definition merge_sort3_safety_wit_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval = (Zlength (l_low_level_spec)))) (PreH2 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH3 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition merge_sort3_safety_wit_2 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort3_safety_wit_3 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_sort3_entail_wit_1 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll x_pre l_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_1_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )
.

Definition merge_sort3_entail_wit_2 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_v: Z) (p_v: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (gmergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll p_v s1 )
  **  (sll q_v s2 )
|--
  EX (l1: (@list Z)) (l2: (@list Z)),
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll p_v l1 )
  **  (sll q_v l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (gmergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((gmergesortrec (s1))) ((gmergesortrec_loc1 (s2)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_2_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (s1: (@list Z)) (s2: (@list Z)) (PreH1 : (safeExec ATrue (applyf (gmergesortrec_loc0) ((maketuple (s1) (s2)))) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (safeExec ATrue (bind ((gmergesortrec (s1))) ((gmergesortrec_loc1 (s2)))) X_low_level_spec )
.

Definition merge_sort3_entail_wit_3 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_v: Z) (l2_2: (@list Z)) (l0: (@list Z)) (retval_2: Z) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll retval_2 l0 )
  **  (sll q_v l2_2 )
|--
  EX (l2: (@list Z)) (l1: (@list Z)),
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll retval_2 l1 )
  **  (sll q_v l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (l2_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  TT && emp 
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_3_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (l2_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((gmergesortrec_loc1 (l2_2))) (l0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (safeExec ATrue (bind ((gmergesortrec (l2_2))) ((mergesortrec_loc2 (l0)))) X_low_level_spec )
.

Definition merge_sort3_entail_wit_4 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (l1_2: (@list Z)) (l0: (@list Z)) (retval_3: Z) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll retval_3 l0 )
  **  (sll retval_2 l1_2 )
|--
  EX (l1: (@list Z)) (l2: (@list Z)),
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll retval_2 l1 )
  **  (sll retval_3 l2 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (l1_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  TT && emp 
|--
  “ (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_entail_wit_4_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (l1_2: (@list Z)) (l0: (@list Z)) (PreH1 : (safeExec ATrue (applyf ((mergesortrec_loc2 (l1_2))) (l0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (safeExec ATrue (merge_rel (l1_2) (l0)) X_low_level_spec )
.

Definition merge_sort3_return_wit_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (s3: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (return (s3)) X_low_level_spec )) (PreH2 : (retval_2 > 8)) (PreH3 : (retval_2 = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll retval s3 )
|--
  EX (l0: (@list Z)),
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll retval l0 )
.

Definition merge_sort3_return_wit_2 :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (l0_2: (@list Z)) (retval: Z) (PreH1 : (Permutation l_low_level_spec l0_2 )) (PreH2 : (incr l0_2 )) (PreH3 : (retval_2 <= 8)) (PreH4 : (retval_2 = (Zlength (l_low_level_spec)))) (PreH5 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH6 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll retval l0_2 )
|--
  EX (l0: (@list Z)),
  “ (safeExec ATrue (return (l0)) X_low_level_spec ) ”
  &&  (sll retval l0 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (l0_2: (@list Z)) (PreH1 : (Permutation l_low_level_spec l0_2 )) (PreH2 : (incr l0_2 )) (PreH3 : (retval_2 <= 8)) (PreH4 : (retval_2 = (Zlength (l_low_level_spec)))) (PreH5 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH6 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  emp
).

Definition merge_sort3_return_wit_2_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval_2: Z) (l0_2: (@list Z)) (PreH1 : (Permutation l_low_level_spec l0_2 )) (PreH2 : (incr l0_2 )) (PreH3 : (retval_2 <= 8)) (PreH4 : (retval_2 = (Zlength (l_low_level_spec)))) (PreH5 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH6 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (safeExec ATrue (return (l0_2)) X_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_1_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH2 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (sll x_pre l_low_level_spec )
|--
  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
.

Definition merge_sort3_partial_solve_wit_1_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (PreH1 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH2 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_1 := merge_sort3_partial_solve_wit_1_pure -> merge_sort3_partial_solve_wit_1_aux.

Definition merge_sort3_partial_solve_wit_2 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval <= 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  “ (retval <= 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_3_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 = 0) ”
.

Definition merge_sort3_partial_solve_wit_3_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_3 := merge_sort3_partial_solve_wit_3_pure -> merge_sort3_partial_solve_wit_3_aux.

Definition merge_sort3_partial_solve_wit_4_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 = 0) ”
.

Definition merge_sort3_partial_solve_wit_4_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (retval > 8)) (PreH2 : (retval = (Zlength (l_low_level_spec)))) (PreH3 : ((Zlength (l_low_level_spec)) <= INT_MAX)) (PreH4 : (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec )),
  (sll 0 (@nil Z) )
  **  (sll x_pre l_low_level_spec )
|--
  “ (0 = 0) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
.

Definition merge_sort3_partial_solve_wit_4 := merge_sort3_partial_solve_wit_4_pure -> merge_sort3_partial_solve_wit_4_aux.

Definition merge_sort3_partial_solve_wit_5_pure :=
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ”
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ”
).

Definition merge_sort3_partial_solve_wit_5_pure_split_goal_1 :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  ((( &( "q" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> 0)
  **  (sll x_pre l_low_level_spec )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_5_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (PreH1 : (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll x_pre l_low_level_spec )
|--
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec) ((@nil Z)) ((@nil Z)))) (gmergesortrec_loc0)) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((split_rel (l_low_level_spec))) (gmergesortrec_loc0)) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll x_pre l_low_level_spec )
  **  (sll 0 (@nil Z) )
  **  (sll 0 (@nil Z) )
.

Definition merge_sort3_partial_solve_wit_5 := merge_sort3_partial_solve_wit_5_pure -> merge_sort3_partial_solve_wit_5_aux.

Definition merge_sort3_partial_solve_wit_6_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (q_v: Z) (p_v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  ((( &( "p" ) )) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_6_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_v: Z) (p_v: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll p_v l1 )
  **  (sll q_v l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l1))) ((gmergesortrec_loc1 (l2)))) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll p_v l1 )
  **  (sll q_v l2 )
.

Definition merge_sort3_partial_solve_wit_6 := merge_sort3_partial_solve_wit_6_pure -> merge_sort3_partial_solve_wit_6_aux.

Definition merge_sort3_partial_solve_wit_7_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (q_v: Z) (retval_2: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  (sll retval_2 l1 )
  **  ((( &( "q" ) )) # Ptr  |-> q_v)
  **  (sll q_v l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_7_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (q_v: Z) (retval_2: Z) (l2: (@list Z)) (l1: (@list Z)) (PreH1 : (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll retval_2 l1 )
  **  (sll q_v l2 )
|--
  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l2))) ((mergesortrec_loc2 (l1)))) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll q_v l2 )
  **  (sll retval_2 l1 )
.

Definition merge_sort3_partial_solve_wit_7 := merge_sort3_partial_solve_wit_7_pure -> merge_sort3_partial_solve_wit_7_aux.

Definition merge_sort3_partial_solve_wit_8_pure :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (x_pre: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  ((( &( "p" ) )) # Ptr  |-> retval_2)
  **  (sll retval_2 l1 )
  **  ((( &( "q" ) )) # Ptr  |-> retval_3)
  **  (sll retval_3 l2 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
.

Definition merge_sort3_partial_solve_wit_8_aux :=
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (l_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (l1: (@list Z)) (l2: (@list Z)) (PreH1 : (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec )) (PreH2 : (retval > 8)) (PreH3 : (retval = (Zlength (l_low_level_spec)))) (PreH4 : ((Zlength (l_low_level_spec)) <= INT_MAX)),
  (sll retval_2 l1 )
  **  (sll retval_3 l2 )
|--
  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  “ (safeExec ATrue (merge_rel (l1) (l2)) X_low_level_spec ) ”
  &&  “ (retval > 8) ”
  &&  “ (retval = (Zlength (l_low_level_spec))) ”
  &&  “ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  (sll retval_2 l1 )
  **  (sll retval_3 l2 )
.

Definition merge_sort3_partial_solve_wit_8 := merge_sort3_partial_solve_wit_8_pure -> merge_sort3_partial_solve_wit_8_aux.

Definition merge_sort3_which_implies_wit_1 :=
forall (p: Z) (PreH1 : (p = 0)),
  TT && emp 
|--
  (sll p (@nil Z) )
.

Definition merge_sort3_which_implies_wit_2 :=
forall (q: Z) (PreH1 : (q = 0)),
  TT && emp 
|--
  (sll q (@nil Z) )
.

(* Shallow FunAssertion specs for merge_sort3. *)
Definition merge_sort3_sig : FuncSig := ([ * struct "list"],  * struct "list")%ctype.

Definition merge_sort3_low_level_spec : Spec merge_sort3_sig :=
  fun F =>
ALL (l: (@list Z)),
ALL (X: ((@list Z) -> (unit -> Prop))),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  (“ ((Zlength (l)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (gmergesortrec (l)) X ) ”
  &&  (sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (return (l0)) X ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort3_low_level_spec_aux : Spec merge_sort3_sig :=
  fun F =>
ALL B : Type,
ALL (l: (@list Z)),
ALL (c: ((@list Z) -> (@ StateRelMonad.M  unit B))),
ALL (X: (B -> (unit -> Prop))),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  (“ ((Zlength (l)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l))) (c)) X ) ”
  &&  (sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (applyf (c) (l0)) X ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort3_high_level_spec : Spec merge_sort3_sig :=
  fun F =>
ALL (l: (@list Z)),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  (“ ((Zlength (l)) <= INT_MAX) ”
  &&  (sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (Permutation l l0 ) ”
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort3_low_level_spec_entail_low_level_spec_aux :=
forall (B: Type),
forall (x_pre: Z) (l_low_level_spec_aux: (@list Z)) (c_low_level_spec_aux: ((@list Z) -> (@ StateRelMonad.M  unit B))) (X_low_level_spec_aux: (B -> (unit -> Prop))),
  (“ ((Zlength (l_low_level_spec_aux)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (bind ((gmergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l_low_level_spec_aux ))
|--
EX (l_low_level_spec: (@list Z))(X_low_level_spec: ((@list Z) -> (unit -> Prop))),
  (“ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l0_2: (@list Z)),
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval l0_2 ))
  -*
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort3_low_level_spec_entail_high_level_spec :=
forall (x_pre: Z) (l_high_level_spec: (@list Z)),
  (“ ((Zlength (l_high_level_spec)) <= INT_MAX) ”
  &&  (sll x_pre l_high_level_spec ))
|--
EX (l_low_level_spec: (@list Z))(X_low_level_spec: ((@list Z) -> (unit -> Prop))),
  (“ ((Zlength (l_low_level_spec)) <= INT_MAX) ”
  &&  “ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l0_2: (@list Z)),
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval l0_2 ))
  -*
  (EX (l0: (@list Z)),
  “ (Permutation l_high_level_spec l0 ) ”
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
.

(* Shallow FunAssertion specs for merge_sort2. *)
Definition merge_sort2_sig : FuncSig := ([ * struct "list"],  * struct "list")%ctype.

Definition merge_sort2_low_level_spec : Spec merge_sort2_sig :=
  fun F =>
ALL (l: (@list Z)),
ALL (X: ((@list Z) -> (unit -> Prop))),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  (“ (safeExec ATrue (gmergesortrec (l)) X ) ”
  &&  (sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (return (l0)) X ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort2_low_level_spec_aux : Spec merge_sort2_sig :=
  fun F =>
ALL B : Type,
ALL (l: (@list Z)),
ALL (c: ((@list Z) -> (@ StateRelMonad.M  unit B))),
ALL (X: (B -> (unit -> Prop))),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  (“ (safeExec ATrue (bind ((gmergesortrec (l))) (c)) X ) ”
  &&  (sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (applyf (c) (l0)) X ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort2_high_level_spec : Spec merge_sort2_sig :=
  fun F =>
ALL (l: (@list Z)),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  ((sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (Permutation l l0 ) ”
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort2_low_level_spec_entail_low_level_spec_aux :=
forall (B: Type),
forall (x_pre: Z) (l_low_level_spec_aux: (@list Z)) (c_low_level_spec_aux: ((@list Z) -> (@ StateRelMonad.M  unit B))) (X_low_level_spec_aux: (B -> (unit -> Prop))),
  (“ (safeExec ATrue (bind ((gmergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l_low_level_spec_aux ))
|--
EX (l_low_level_spec: (@list Z))(X_low_level_spec: ((@list Z) -> (unit -> Prop))),
  (“ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l0_2: (@list Z)),
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval l0_2 ))
  -*
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort2_low_level_spec_entail_high_level_spec :=
forall (x_pre: Z) (l_high_level_spec: (@list Z)),
  ((sll x_pre l_high_level_spec ))
|--
EX (l_low_level_spec: (@list Z))(X_low_level_spec: ((@list Z) -> (unit -> Prop))),
  (“ (safeExec ATrue (gmergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l0_2: (@list Z)),
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval l0_2 ))
  -*
  (EX (l0: (@list Z)),
  “ (Permutation l_high_level_spec l0 ) ”
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
.

(* Shallow FunAssertion specs for merge_sort. *)
Definition merge_sort_sig : FuncSig := ([ * struct "list"],  * struct "list")%ctype.

Definition merge_sort_low_level_spec : Spec merge_sort_sig :=
  fun F =>
ALL (l: (@list Z)),
ALL (X: ((@list Z) -> (unit -> Prop))),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  (“ (safeExec ATrue (mergesortrec (l)) X ) ”
  &&  (sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (return (l0)) X ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort_low_level_spec_aux : Spec merge_sort_sig :=
  fun F =>
ALL B : Type,
ALL (l: (@list Z)),
ALL (c: ((@list Z) -> (@ StateRelMonad.M  unit B))),
ALL (X: (B -> (unit -> Prop))),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  (“ (safeExec ATrue (bind ((mergesortrec (l))) (c)) X ) ”
  &&  (sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (applyf (c) (l0)) X ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort_high_level_spec : Spec merge_sort_sig :=
  fun F =>
ALL (l: (@list Z)),
HoareFun ([ * struct "list"],  * struct "list")%ctype
  (fun x_pre =>
  ((sll x_pre l )))
  (fun x_pre retval =>
  (EX (l0: (@list Z)),
  “ (Permutation l l0 ) ”
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
  F.

Definition merge_sort_low_level_spec_entail_low_level_spec_aux :=
forall (B: Type),
forall (x_pre: Z) (l_low_level_spec_aux: (@list Z)) (c_low_level_spec_aux: ((@list Z) -> (@ StateRelMonad.M  unit B))) (X_low_level_spec_aux: (B -> (unit -> Prop))),
  (“ (safeExec ATrue (bind ((mergesortrec (l_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l_low_level_spec_aux ))
|--
EX (l_low_level_spec: (@list Z))(X_low_level_spec: ((@list Z) -> (unit -> Prop))),
  (“ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l0_2: (@list Z)),
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval l0_2 ))
  -*
  (EX (l0: (@list Z)),
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) (l0)) X_low_level_spec_aux ) ”
  &&  (sll retval l0 )))
.

Definition merge_sort_low_level_spec_entail_high_level_spec :=
forall (x_pre: Z) (l_high_level_spec: (@list Z)),
  ((sll x_pre l_high_level_spec ))
|--
EX (l_low_level_spec: (@list Z))(X_low_level_spec: ((@list Z) -> (unit -> Prop))),
  (“ (safeExec ATrue (mergesortrec (l_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec ))
  **
  (ALL (retval: Z),
  (EX (l0_2: (@list Z)),
  “ (safeExec ATrue (return (l0_2)) X_low_level_spec ) ”
  &&  (sll retval l0_2 ))
  -*
  (EX (l0: (@list Z)),
  “ (Permutation l_high_level_spec l0 ) ”
  &&  “ (incr l0 ) ”
  &&  (sll retval l0 )))
.

(* Shallow FunAssertion specs for split_rec. *)
Definition split_rec_sig : FuncSig := ([ * struct "list";  *  * struct "list";  *  * struct "list"], void)%ctype.

Definition split_rec_low_level_spec : Spec split_rec_sig :=
  fun F =>
ALL (l: (@list Z)),
ALL (l1: (@list Z)),
ALL (l2: (@list Z)),
ALL (X: (((@list Z) * (@list Z)) -> (unit -> Prop))),
HoareFun ([ * struct "list";  *  * struct "list";  *  * struct "list"], void)%ctype
  (fun '(x_pre, (p_pre, q_pre)) =>
  (EX (q_v: Z) (p_v: Z),
  “ (safeExec ATrue (split_rec_rel (l) (l1) (l2)) X ) ”
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )))
  (fun '(x_pre, (p_pre, q_pre)) (_retval : unit) =>
  (EX (q_v_2: Z) (p_v_2: Z) (s1: (@list Z)) (s2: (@list Z)),
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X ) ”
  &&  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 s1 )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 s2 )))
  F.

Definition split_rec_low_level_spec_aux : Spec split_rec_sig :=
  fun F =>
ALL B : Type,
ALL (l: (@list Z)),
ALL (l1: (@list Z)),
ALL (l2: (@list Z)),
ALL (c: (((@list Z) * (@list Z)) -> (@ StateRelMonad.M  unit B))),
ALL (X: (B -> (unit -> Prop))),
HoareFun ([ * struct "list";  *  * struct "list";  *  * struct "list"], void)%ctype
  (fun '(x_pre, (p_pre, q_pre)) =>
  (EX (q_v: Z) (p_v: Z),
  “ (safeExec ATrue (bind ((split_rec_rel (l) (l1) (l2))) (c)) X ) ”
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1 )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2 )))
  (fun '(x_pre, (p_pre, q_pre)) (_retval : unit) =>
  (EX (q_v_2: Z) (p_v_2: Z) (s1: (@list Z)) (s2: (@list Z)),
  “ (safeExec ATrue (applyf (c) ((maketuple (s1) (s2)))) X ) ”
  &&  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 s1 )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 s2 )))
  F.

Definition split_rec_high_level_spec : Spec split_rec_sig :=
  fun F =>
ALL (l: (@list Z)),
ALL (X: (((@list Z) * (@list Z)) -> (unit -> Prop))),
HoareFun ([ * struct "list";  *  * struct "list";  *  * struct "list"], void)%ctype
  (fun '(x_pre, (p_pre, q_pre)) =>
  (EX (q_v: Z) (p_v: Z),
  “ (safeExec ATrue (split_rel (l)) X ) ”
  &&  (sll x_pre l )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v (@nil Z) )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v (@nil Z) )))
  (fun '(x_pre, (p_pre, q_pre)) (_retval : unit) =>
  (EX (q_v_2: Z) (p_v_2: Z) (s1: (@list Z)) (s2: (@list Z)),
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X ) ”
  &&  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 s1 )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 s2 )))
  F.

Definition split_rec_low_level_spec_entail_low_level_spec_aux :=
forall (B: Type),
forall (x_pre: Z) (p_pre: Z) (q_pre: Z) (l_low_level_spec_aux: (@list Z)) (l1_low_level_spec_aux: (@list Z)) (l2_low_level_spec_aux: (@list Z)) (c_low_level_spec_aux: (((@list Z) * (@list Z)) -> (@ StateRelMonad.M  unit B))) (X_low_level_spec_aux: (B -> (unit -> Prop))),
  (EX (q_v: Z) (p_v: Z),
  “ (safeExec ATrue (bind ((split_rec_rel (l_low_level_spec_aux) (l1_low_level_spec_aux) (l2_low_level_spec_aux))) (c_low_level_spec_aux)) X_low_level_spec_aux ) ”
  &&  (sll x_pre l_low_level_spec_aux )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v l1_low_level_spec_aux )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v l2_low_level_spec_aux ))
|--
EX (l_low_level_spec: (@list Z))(l1_low_level_spec: (@list Z))(l2_low_level_spec: (@list Z))(X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))),
  (EX (q_v_3: Z) (p_v_3: Z),
  “ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_v_3)
  **  (sll p_v_3 l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v_3)
  **  (sll q_v_3 l2_low_level_spec ))
  **
  (  (EX (q_v_4: Z) (p_v_4: Z) (s1_2: (@list Z)) (s2_2: (@list Z)),
  “ (safeExec ATrue (return ((maketuple (s1_2) (s2_2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> p_v_4)
  **  (sll p_v_4 s1_2 )
  **  ((q_pre) # Ptr  |-> q_v_4)
  **  (sll q_v_4 s2_2 ))
  -*
  (EX (q_v_2: Z) (p_v_2: Z) (s1: (@list Z)) (s2: (@list Z)),
  “ (safeExec ATrue (applyf (c_low_level_spec_aux) ((maketuple (s1) (s2)))) X_low_level_spec_aux ) ”
  &&  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 s1 )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 s2 )))
.

Definition split_rec_low_level_spec_entail_high_level_spec :=
forall (x_pre: Z) (p_pre: Z) (q_pre: Z) (l_high_level_spec: (@list Z)) (X_high_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))),
  (EX (q_v: Z) (p_v: Z),
  “ (safeExec ATrue (split_rel (l_high_level_spec)) X_high_level_spec ) ”
  &&  (sll x_pre l_high_level_spec )
  **  ((p_pre) # Ptr  |-> p_v)
  **  (sll p_v nil )
  **  ((q_pre) # Ptr  |-> q_v)
  **  (sll q_v nil ))
|--
EX (l_low_level_spec: (@list Z))(l1_low_level_spec: (@list Z))(l2_low_level_spec: (@list Z))(X_low_level_spec: (((@list Z) * (@list Z)) -> (unit -> Prop))),
  (EX (q_v_3: Z) (p_v_3: Z),
  “ (safeExec ATrue (split_rec_rel (l_low_level_spec) (l1_low_level_spec) (l2_low_level_spec)) X_low_level_spec ) ”
  &&  (sll x_pre l_low_level_spec )
  **  ((p_pre) # Ptr  |-> p_v_3)
  **  (sll p_v_3 l1_low_level_spec )
  **  ((q_pre) # Ptr  |-> q_v_3)
  **  (sll q_v_3 l2_low_level_spec ))
  **
  (  (EX (q_v_4: Z) (p_v_4: Z) (s1_2: (@list Z)) (s2_2: (@list Z)),
  “ (safeExec ATrue (return ((maketuple (s1_2) (s2_2)))) X_low_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> p_v_4)
  **  (sll p_v_4 s1_2 )
  **  ((q_pre) # Ptr  |-> q_v_4)
  **  (sll q_v_4 s2_2 ))
  -*
  (EX (q_v_2: Z) (p_v_2: Z) (s1: (@list Z)) (s2: (@list Z)),
  “ (safeExec ATrue (return ((maketuple (s1) (s2)))) X_high_level_spec ) ”
  &&  ((p_pre) # Ptr  |-> p_v_2)
  **  (sll p_v_2 s1 )
  **  ((q_pre) # Ptr  |-> q_v_2)
  **  (sll q_v_2 s2 )))
.

Module Type VC_Correct.

Include sll_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Axiom proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Axiom proof_of_merge_safety_wit_3 : merge_safety_wit_3.
Axiom proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Axiom proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Axiom proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Axiom proof_of_merge_return_wit_1 : merge_return_wit_1.
Axiom proof_of_merge_return_wit_2 : merge_return_wit_2.
Axiom proof_of_merge_partial_solve_wit_1_pure : merge_partial_solve_wit_1_pure.
Axiom proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Axiom proof_of_merge_partial_solve_wit_2_pure : merge_partial_solve_wit_2_pure.
Axiom proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Axiom proof_of_merge_partial_solve_wit_3 : merge_partial_solve_wit_3.
Axiom proof_of_merge_partial_solve_wit_4 : merge_partial_solve_wit_4.
Axiom proof_of_merge_which_implies_wit_1 : merge_which_implies_wit_1.
Axiom proof_of_merge_which_implies_wit_2 : merge_which_implies_wit_2.
Axiom proof_of_merge_which_implies_wit_3 : merge_which_implies_wit_3.
Axiom proof_of_split_rec_safety_wit_1 : split_rec_safety_wit_1.
Axiom proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Axiom proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Axiom proof_of_split_rec_partial_solve_wit_1_pure : split_rec_partial_solve_wit_1_pure.
Axiom proof_of_split_rec_partial_solve_wit_1 : split_rec_partial_solve_wit_1.
Axiom proof_of_split_rec_partial_solve_wit_2_pure : split_rec_partial_solve_wit_2_pure.
Axiom proof_of_split_rec_partial_solve_wit_2 : split_rec_partial_solve_wit_2.
Axiom proof_of_split_rec_partial_solve_wit_3_pure : split_rec_partial_solve_wit_3_pure.
Axiom proof_of_split_rec_partial_solve_wit_3 : split_rec_partial_solve_wit_3.
Axiom proof_of_split_rec_which_implies_wit_1 : split_rec_which_implies_wit_1.
Axiom proof_of_split_rec_which_implies_wit_2 : split_rec_which_implies_wit_2.
Axiom proof_of_merge_sort_safety_wit_1 : merge_sort_safety_wit_1.
Axiom proof_of_merge_sort_safety_wit_2 : merge_sort_safety_wit_2.
Axiom proof_of_merge_sort_safety_wit_3 : merge_sort_safety_wit_3.
Axiom proof_of_merge_sort_entail_wit_1 : merge_sort_entail_wit_1.
Axiom proof_of_merge_sort_entail_wit_2 : merge_sort_entail_wit_2.
Axiom proof_of_merge_sort_entail_wit_3 : merge_sort_entail_wit_3.
Axiom proof_of_merge_sort_entail_wit_4 : merge_sort_entail_wit_4.
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
Axiom proof_of_merge_sort_partial_solve_wit_5_pure : merge_sort_partial_solve_wit_5_pure.
Axiom proof_of_merge_sort_partial_solve_wit_5 : merge_sort_partial_solve_wit_5.
Axiom proof_of_merge_sort_partial_solve_wit_6_pure : merge_sort_partial_solve_wit_6_pure.
Axiom proof_of_merge_sort_partial_solve_wit_6 : merge_sort_partial_solve_wit_6.
Axiom proof_of_merge_sort_which_implies_wit_1 : merge_sort_which_implies_wit_1.
Axiom proof_of_merge_sort_which_implies_wit_2 : merge_sort_which_implies_wit_2.
Axiom proof_of_merge_sort3_safety_wit_1 : merge_sort3_safety_wit_1.
Axiom proof_of_merge_sort3_safety_wit_2 : merge_sort3_safety_wit_2.
Axiom proof_of_merge_sort3_safety_wit_3 : merge_sort3_safety_wit_3.
Axiom proof_of_merge_sort3_entail_wit_1 : merge_sort3_entail_wit_1.
Axiom proof_of_merge_sort3_entail_wit_2 : merge_sort3_entail_wit_2.
Axiom proof_of_merge_sort3_entail_wit_3 : merge_sort3_entail_wit_3.
Axiom proof_of_merge_sort3_entail_wit_4 : merge_sort3_entail_wit_4.
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
Axiom proof_of_merge_sort3_partial_solve_wit_7_pure : merge_sort3_partial_solve_wit_7_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_7 : merge_sort3_partial_solve_wit_7.
Axiom proof_of_merge_sort3_partial_solve_wit_8_pure : merge_sort3_partial_solve_wit_8_pure.
Axiom proof_of_merge_sort3_partial_solve_wit_8 : merge_sort3_partial_solve_wit_8.
Axiom proof_of_merge_sort3_which_implies_wit_1 : merge_sort3_which_implies_wit_1.
Axiom proof_of_merge_sort3_which_implies_wit_2 : merge_sort3_which_implies_wit_2.
Axiom proof_of_merge_sort3_low_level_spec_entail_low_level_spec_aux : merge_sort3_low_level_spec_entail_low_level_spec_aux.
Axiom proof_of_merge_sort3_low_level_spec_entail_high_level_spec : merge_sort3_low_level_spec_entail_high_level_spec.
Axiom proof_of_merge_sort2_low_level_spec_entail_low_level_spec_aux : merge_sort2_low_level_spec_entail_low_level_spec_aux.
Axiom proof_of_merge_sort2_low_level_spec_entail_high_level_spec : merge_sort2_low_level_spec_entail_high_level_spec.
Axiom proof_of_merge_sort_low_level_spec_entail_low_level_spec_aux : merge_sort_low_level_spec_entail_low_level_spec_aux.
Axiom proof_of_merge_sort_low_level_spec_entail_high_level_spec : merge_sort_low_level_spec_entail_high_level_spec.
Axiom proof_of_split_rec_low_level_spec_entail_low_level_spec_aux : split_rec_low_level_spec_entail_low_level_spec_aux.
Axiom proof_of_split_rec_low_level_spec_entail_high_level_spec : split_rec_low_level_spec_entail_high_level_spec.

End VC_Correct.
