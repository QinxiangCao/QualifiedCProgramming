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
Require Import SimpleC.EE.Applications_human.typeinfer.typeinfer_lib.
Local Open Scope sac.
Require Import typeinfer_strategy_goal.
Require Import typeinfer_strategy_proof.

(*----- Function atype_unify -----*)

Definition atype_unify_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1_verify )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify_return_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_verify tr2_verify s_pre_verify s_post_3 )) (PreH3 : (t1_t <> 3)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_verify tr2_verify s_pre_verify s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_return_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (t1_t: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (t1_t <> 3)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_return_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_verify tr2_verify s_pre_verify s_post_3 )) (PreH3 : (tr = None)) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr1_verify = (TVar (n)))) (PreH7 : (t1_t = 3)) (PreH8 : (retval_2 = 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_verify tr2_verify s_pre_verify s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_return_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = None)) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval_2 = 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_return_wit_5 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel (TVar (n)) tr2_verify s_pre_verify s_post_3 )) (PreH3 : (tr = (Some (tr_2)))) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr1_verify = (TVar (n)))) (PreH7 : (t1_t = 3)) (PreH8 : (retval_2 <> 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t2_pre tr2_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_verify tr2_verify s_pre_verify s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
) \/
(
forall (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel (TVar (n)) tr2_verify s_pre_verify s_post_3 )) (PreH7 : (tr = (Some (tr_2)))) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr1_verify = (TVar (n)))) (PreH11 : (t1_t = 3)) (PreH12 : (retval_2 <> 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t1_pre tr1_verify )
).

Definition atype_unify_return_wit_5_split_goal_spatial := 
forall (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel (TVar (n)) tr2_verify s_pre_verify s_post_3 )) (PreH7 : (tr = (Some (tr_2)))) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr1_verify = (TVar (n)))) (PreH11 : (t1_t = 3)) (PreH12 : (retval_2 <> 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t1_pre tr1_verify )
.

Definition atype_unify_return_wit_6 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval_2 <> 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t2_pre tr2_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
) \/
(
forall (t1_pre: Z) (tr1_verify: TypeTree) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (tr = (Some (tr_2)))) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr1_verify = (TVar (n)))) (PreH10 : (t1_t = 3)) (PreH11 : (retval_2 <> 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t1_pre tr1_verify )
).

Definition atype_unify_return_wit_6_split_goal_spatial := 
forall (t1_pre: Z) (tr1_verify: TypeTree) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (tr = (Some (tr_2)))) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr1_verify = (TVar (n)))) (PreH10 : (t1_t = 3)) (PreH11 : (retval_2 <> 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t1_pre tr1_verify )
.

Definition atype_unify_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) ,
  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
|--
  (store_type t1_pre tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (PreH1 : (t1_t = 3)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1_verify )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (3 = 3) ”
.

Definition atype_unify_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (PreH1 : (t1_t = 3)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (3 = 3) ” 
  &&  “ (t1_t = 3) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t1_pre 3 tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_2 := atype_unify_partial_solve_wit_2_pure -> atype_unify_partial_solve_wit_2_aux.

Definition atype_unify_partial_solve_wit_3_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (PreH1 : (3 = 3)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1_verify = (TVar (n)))) (PreH5 : (t1_t = 3)) ,
  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ”
.

Definition atype_unify_partial_solve_wit_3_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (PreH1 : (3 = 3)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1_verify = (TVar (n)))) (PreH5 : (t1_t = 3)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_3 := atype_unify_partial_solve_wit_3_pure -> atype_unify_partial_solve_wit_3_aux.

Definition atype_unify_partial_solve_wit_4_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr1_verify = (TVar (n)))) (PreH4 : (t1_t = 3)) (PreH5 : (retval <> 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre_verify n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2_verify )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ”
.

Definition atype_unify_partial_solve_wit_4_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr1_verify = (TVar (n)))) (PreH4 : (t1_t = 3)) (PreH5 : (retval <> 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre_verify n retval tr )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t2_pre tr2_verify )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n retval tr )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_4 := atype_unify_partial_solve_wit_4_pure -> atype_unify_partial_solve_wit_4_aux.

Definition atype_unify_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr_2: (@option TypeTree)) (retval: Z) (tr: TypeTree) (PreH1 : (tr_2 = (Some (tr)))) (PreH2 : (solution_at s_pre_verify n tr )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval <> 0)) ,
  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2_verify )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (solution_at s_pre_verify n tr ) ”
.

Definition atype_unify_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr_2: (@option TypeTree)) (retval: Z) (tr: TypeTree) (PreH1 : (tr_2 = (Some (tr)))) (PreH2 : (solution_at s_pre_verify n tr )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval <> 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2_verify )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (solution_at s_pre_verify n tr ) ” 
  &&  “ (tr_2 = (Some (tr))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_5 := atype_unify_partial_solve_wit_5_pure -> atype_unify_partial_solve_wit_5_aux.

Definition atype_unify_partial_solve_wit_6_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (PreH1 : (repr_rel_node s_pre_verify (TVar (n)) tr_repr )) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval <> 0)) ,
  ((( &( "r" ) )) # Int  |->_)
  **  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> retval_2)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2_verify )
|--
  “ (repr_rel_node s_pre_verify (TVar (n)) tr_repr ) ”
.

Definition atype_unify_partial_solve_wit_6_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (PreH1 : (repr_rel_node s_pre_verify (TVar (n)) tr_repr )) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval <> 0)) ,
  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t2_pre tr2_verify )
|--
  “ (repr_rel_node s_pre_verify (TVar (n)) tr_repr ) ” 
  &&  “ (tr = (Some (tr_2))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type retval_2 tr_repr )
  **  (store_type t2_pre tr2_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify_partial_solve_wit_6 := atype_unify_partial_solve_wit_6_pure -> atype_unify_partial_solve_wit_6_aux.

Definition atype_unify_partial_solve_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (unify_rel (TVar (n)) tr2_verify s_pre_verify s_post )) (PreH3 : (tr = (Some (tr_2)))) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr1_verify = (TVar (n)))) (PreH7 : (t1_t = 3)) (PreH8 : (retval <> 0)) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type retval_2 tr_repr )
  **  (store_type t2_pre tr2_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  “ (retval_3 = 0) ” 
  &&  “ (unify_rel (TVar (n)) tr2_verify s_pre_verify s_post ) ” 
  &&  “ (tr = (Some (tr_2))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t2_pre tr2_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify_partial_solve_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval <> 0)) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type retval_2 tr_repr )
  **  (store_type t2_pre tr2_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  “ (retval_3 <> 0) ” 
  &&  “ (tr = (Some (tr_2))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t2_pre tr2_verify )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify_partial_solve_wit_9_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr1_verify = (TVar (n)))) (PreH4 : (t1_t = 3)) (PreH5 : (retval = 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre_verify n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2_verify )
|--
  “ (0 = 0) ” 
  &&  “ (3 = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ”
.

Definition atype_unify_partial_solve_wit_9_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr1_verify = (TVar (n)))) (PreH4 : (t1_t = 3)) (PreH5 : (retval = 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre_verify n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t2_pre tr2_verify )
|--
  “ (0 = 0) ” 
  &&  “ (3 = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (retval = 0) ”
  &&  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n 0 tr )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_9 := atype_unify_partial_solve_wit_9_pure -> atype_unify_partial_solve_wit_9_aux.

Definition atype_unify_partial_solve_wit_10_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (tr = None)) (PreH2 : (repr_rel_node s_pre_verify tr1_verify tr1_verify )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval = 0)) ,
  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1_verify )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2_verify )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ”
.

Definition atype_unify_partial_solve_wit_10_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (tr = None)) (PreH2 : (repr_rel_node s_pre_verify tr1_verify tr1_verify )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (retval = 0)) ,
  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ” 
  &&  “ (tr = None) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (retval = 0) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_10 := atype_unify_partial_solve_wit_10_pure -> atype_unify_partial_solve_wit_10_aux.

Definition atype_unify_partial_solve_wit_11_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (PreH1 : (t1_t <> 3)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1_verify )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (t1_t <> 3) ”
.

Definition atype_unify_partial_solve_wit_11_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (PreH1 : (t1_t <> 3)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (t1_t <> 3) ” 
  &&  “ (t1_t <> 3) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_11 := atype_unify_partial_solve_wit_11_pure -> atype_unify_partial_solve_wit_11_aux.

Definition atype_unify_partial_solve_wit_12_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (PreH1 : (repr_rel_node s_pre_verify tr1_verify tr1_verify )) (PreH2 : (t1_t <> 3)) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2_verify )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ”
.

Definition atype_unify_partial_solve_wit_12_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_verify: TypeTree) (tr1_verify: TypeTree) (s_pre_verify: sol) (t1_t: Z) (PreH1 : (repr_rel_node s_pre_verify tr1_verify tr1_verify )) (PreH2 : (t1_t <> 3)) ,
  (store_type t1_pre tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t2_pre tr2_verify )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ” 
  &&  “ (t1_t <> 3) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )
.

Definition atype_unify_partial_solve_wit_12 := atype_unify_partial_solve_wit_12_pure -> atype_unify_partial_solve_wit_12_aux.

Definition atype_unify_which_implies_wit_1 := 
(
forall (tr1_verify: TypeTree) (t1: Z) ,
  (store_type t1 tr1_verify )
|--
  EX (t1_t: Z) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1_verify )
) \/
(
forall (tr1_verify: TypeTree) (t1: Z) ,
  (store_type t1 tr1_verify )
|--
  EX (t1_t: Z) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1_verify )
).

Definition atype_unify_which_implies_wit_2 := 
(
forall (tr1_verify: TypeTree) (t1: Z) (t1_t: Z) (PreH1 : (t1_t = 3)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1_verify )
|--
  EX (n: Z) ,
  “ (t1_t = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ”
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
) \/
(
forall (tr1_verify: TypeTree) (t1: Z) (t1_t: Z) (PreH1 : (t1_t = 3)) ,
  (store_type_aux t1 t1_t tr1_verify )
|--
  EX (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1_verify = (TVar (n))) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
).

Definition atype_unify_which_implies_wit_3 := 
(
forall (s_pre_verify: sol) (n: Z) (tr_opt: (@option TypeTree)) (t1: Z) (tp: Z) (PreH1 : (tp <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) ,
  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n tp tr_opt )
|--
  EX (tr: TypeTree) ,
  “ (tr_opt = (Some (tr))) ” 
  &&  “ (solution_at s_pre_verify n tr ) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre_verify )
) \/
(
forall (s_pre_verify: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (PreH1 : (tp <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) ,
  (store_solution_aux ( &( "res" ) ) s_pre_verify n tp tr_opt )
|--
  EX (tr: TypeTree) ,
  “ (tr_opt = (Some (tr))) ” 
  &&  “ (solution_at s_pre_verify n tr ) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
).

Definition atype_unify_which_implies_wit_4 := 
(
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t1: Z) (t1_t: Z) (PreH1 : (tp = 0)) (PreH2 : (t1_t = 3)) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1_verify = (TVar (n)))) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n tp tr_opt )
|--
  “ (tr_opt = None) ” 
  &&  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1 tr1_verify )
) \/
(
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t1: Z) (t1_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t1_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t1_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t1_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr1_verify = (TVar (n)))) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n tp tr_opt )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ” 
  &&  “ (tr_opt = None) ”
  &&  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1 tr1_verify )
).

Definition atype_unify_which_implies_wit_4_split_goal_1 := 
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t1: Z) (t1_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t1_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t1_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t1_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr1_verify = (TVar (n)))) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n tp tr_opt )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ”
.

Definition atype_unify_which_implies_wit_4_split_goal_2 := 
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t1: Z) (t1_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t1_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t1_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t1_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr1_verify = (TVar (n)))) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n tp tr_opt )
|--
  “ (tr_opt = None) ”
.

Definition atype_unify_which_implies_wit_4_split_goal_spatial := 
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t1: Z) (t1_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t1_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t1_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t1_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr1_verify = (TVar (n)))) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre_verify n tp tr_opt )
|--
  (store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1 tr1_verify )
.

Definition atype_unify_which_implies_wit_5 := 
(
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (t1: Z) (t1_t: Z) (PreH1 : (t1_t <> 3)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ”
  &&  (store_type t1 tr1_verify )
  **  (store_solution ( &( "res" ) ) s_pre_verify )
) \/
(
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (t1: Z) (t1_t: Z) (PreH1 : (t1_t <= INT_MAX)) (PreH2 : (t1_t >= INT_MIN)) (PreH3 : (t1_t <> 3)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1_verify )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ”
  &&  (store_type t1 tr1_verify )
).

Definition atype_unify_which_implies_wit_5_split_goal_1 := 
forall (tr1_verify: TypeTree) (s_pre_verify: sol) (t1: Z) (t1_t: Z) (PreH1 : (t1_t <= INT_MAX)) (PreH2 : (t1_t >= INT_MIN)) (PreH3 : (t1_t <> 3)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1_verify )
|--
  “ (repr_rel_node s_pre_verify tr1_verify tr1_verify ) ”
.

Definition atype_unify_which_implies_wit_5_split_goal_spatial := 
forall (tr1_verify: TypeTree) (t1: Z) (t1_t: Z) (PreH1 : (t1_t <= INT_MAX)) (PreH2 : (t1_t >= INT_MIN)) (PreH3 : (t1_t <> 3)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1_verify )
|--
  (store_type t1 tr1_verify )
.

(*----- Function atype_unify1 -----*)

Definition atype_unify1_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (PreH1 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify1_return_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_prev tr2 s_pre s_post_3 )) (PreH3 : (t2_t <> 3)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_prev tr2 s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_return_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (t2_t: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (t2_t <> 3)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_return_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_prev tr2 s_pre s_post_3 )) (PreH3 : (tr = None)) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr2 = (TVar (n)))) (PreH7 : (t2_t = 3)) (PreH8 : (retval_2 = 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_prev tr2 s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_return_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = None)) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (retval_2 = 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_return_wit_5 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_prev (TVar (n)) s_pre s_post_3 )) (PreH3 : (tr = (Some (tr_2)))) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr2 = (TVar (n)))) (PreH7 : (t2_t = 3)) (PreH8 : (retval_2 <> 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_prev tr2 s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_prev (TVar (n)) s_pre s_post_3 )) (PreH7 : (tr = (Some (tr_2)))) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr2 = (TVar (n)))) (PreH11 : (t2_t = 3)) (PreH12 : (retval_2 <> 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t2_pre tr2 )
).

Definition atype_unify1_return_wit_5_split_goal_spatial := 
forall (t2_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_prev (TVar (n)) s_pre s_post_3 )) (PreH7 : (tr = (Some (tr_2)))) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr2 = (TVar (n)))) (PreH11 : (t2_t = 3)) (PreH12 : (retval_2 <> 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t2_pre tr2 )
.

Definition atype_unify1_return_wit_6 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (retval_2 <> 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (tr2: TypeTree) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (tr = (Some (tr_2)))) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr2 = (TVar (n)))) (PreH10 : (t2_t = 3)) (PreH11 : (retval_2 <> 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t2_pre tr2 )
).

Definition atype_unify1_return_wit_6_split_goal_spatial := 
forall (t2_pre: Z) (tr2: TypeTree) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval_2: Z) (tr_2: TypeTree) (retval: Z) (PreH1 : (3 <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (3 >= INT_MIN)) (PreH4 : (n >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (tr = (Some (tr_2)))) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr2 = (TVar (n)))) (PreH10 : (t2_t = 3)) (PreH11 : (retval_2 <> 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  (store_type t2_pre tr2 )
.

Definition atype_unify1_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (PreH1 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ”
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (PreH1 : (t2_t = 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (3 = 3) ”
.

Definition atype_unify1_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (PreH1 : (t2_t = 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (3 = 3) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t2_pre 3 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_2 := atype_unify1_partial_solve_wit_2_pure -> atype_unify1_partial_solve_wit_2_aux.

Definition atype_unify1_partial_solve_wit_3_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (PreH1 : (3 = 3)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((( &( "tp" ) )) # Ptr  |->_)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ”
.

Definition atype_unify1_partial_solve_wit_3_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (PreH1 : (3 = 3)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_3 := atype_unify1_partial_solve_wit_3_pure -> atype_unify1_partial_solve_wit_3_aux.

Definition atype_unify1_partial_solve_wit_4_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr2 = (TVar (n)))) (PreH4 : (t2_t = 3)) (PreH5 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH6 : (retval <> 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ”
.

Definition atype_unify1_partial_solve_wit_4_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr2 = (TVar (n)))) (PreH4 : (t2_t = 3)) (PreH5 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH6 : (retval <> 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t1_pre tr1 )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_4 := atype_unify1_partial_solve_wit_4_pure -> atype_unify1_partial_solve_wit_4_aux.

Definition atype_unify1_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr_2: (@option TypeTree)) (retval: Z) (tr: TypeTree) (PreH1 : (tr_2 = (Some (tr)))) (PreH2 : (solution_at s_pre n tr )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (retval <> 0)) ,
  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (solution_at s_pre n tr ) ”
.

Definition atype_unify1_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr_2: (@option TypeTree)) (retval: Z) (tr: TypeTree) (PreH1 : (tr_2 = (Some (tr)))) (PreH2 : (solution_at s_pre n tr )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (retval <> 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (solution_at s_pre n tr ) ” 
  &&  “ (tr_2 = (Some (tr))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_5 := atype_unify1_partial_solve_wit_5_pure -> atype_unify1_partial_solve_wit_5_aux.

Definition atype_unify1_partial_solve_wit_6_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (PreH1 : (repr_rel_node s_pre (TVar (n)) tr_repr )) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (retval <> 0)) ,
  ((( &( "r" ) )) # Int  |->_)
  **  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> retval_2)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre (TVar (n)) tr_repr ) ”
.

Definition atype_unify1_partial_solve_wit_6_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (PreH1 : (repr_rel_node s_pre (TVar (n)) tr_repr )) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (retval <> 0)) ,
  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type t1_pre tr1 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre (TVar (n)) tr_repr ) ” 
  &&  “ (tr = (Some (tr_2))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr_repr )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify1_partial_solve_wit_6 := atype_unify1_partial_solve_wit_6_pure -> atype_unify1_partial_solve_wit_6_aux.

Definition atype_unify1_partial_solve_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (unify_rel tr1_prev (TVar (n)) s_pre s_post )) (PreH3 : (tr = (Some (tr_2)))) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr2 = (TVar (n)))) (PreH7 : (t2_t = 3)) (PreH8 : (retval <> 0)) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr_repr )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  “ (retval_3 = 0) ” 
  &&  “ (unify_rel tr1_prev (TVar (n)) s_pre s_post ) ” 
  &&  “ (tr = (Some (tr_2))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify1_partial_solve_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2: TypeTree) (tr1: TypeTree) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (tr_2: TypeTree) (tr_repr: TypeTree) (retval_2: Z) (s_post: sol) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (tr = (Some (tr_2)))) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (retval <> 0)) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr_repr )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
|--
  “ (retval_3 <> 0) ” 
  &&  “ (tr = (Some (tr_2))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type retval_2 tr_repr )
  **  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
.

Definition atype_unify1_partial_solve_wit_9_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr2 = (TVar (n)))) (PreH4 : (t2_t = 3)) (PreH5 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH6 : (retval = 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  “ (0 = 0) ” 
  &&  “ (3 = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ”
.

Definition atype_unify1_partial_solve_wit_9_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr2 = (TVar (n)))) (PreH4 : (t2_t = 3)) (PreH5 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH6 : (retval = 0)) ,
  (store_solution_aux ( &( "res" ) ) s_pre n retval tr )
  **  ((( &( "tp" ) )) # Ptr  |-> retval)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_type t1_pre tr1 )
|--
  “ (0 = 0) ” 
  &&  “ (3 = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (retval = 0) ”
  &&  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n 0 tr )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_9 := atype_unify1_partial_solve_wit_9_pure -> atype_unify1_partial_solve_wit_9_aux.

Definition atype_unify1_partial_solve_wit_10_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (tr = None)) (PreH2 : (repr_rel_node s_pre tr2 tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (retval = 0)) ,
  ((( &( "tp" ) )) # Ptr  |-> 0)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2 tr2 ) ”
.

Definition atype_unify1_partial_solve_wit_10_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (n: Z) (tr: (@option TypeTree)) (retval: Z) (PreH1 : (tr = None)) (PreH2 : (repr_rel_node s_pre tr2 tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (retval = 0)) ,
  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
  **  (store_type t1_pre tr1 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2 tr2 ) ” 
  &&  “ (tr = None) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (retval = 0) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_partial_solve_wit_10 := atype_unify1_partial_solve_wit_10_pure -> atype_unify1_partial_solve_wit_10_aux.

Definition atype_unify1_partial_solve_wit_11_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (PreH1 : (t2_t <> 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (t2_t <> 3) ”
.

Definition atype_unify1_partial_solve_wit_11_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (PreH1 : (t2_t <> 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (t2_t <> 3) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
.

Definition atype_unify1_partial_solve_wit_11 := atype_unify1_partial_solve_wit_11_pure -> atype_unify1_partial_solve_wit_11_aux.

Definition atype_unify1_partial_solve_wit_12_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (PreH1 : (repr_rel_node s_pre tr2 tr2 )) (PreH2 : (t2_t <> 3)) (PreH3 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2 tr2 ) ”
.

Definition atype_unify1_partial_solve_wit_12_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t2_t: Z) (PreH1 : (repr_rel_node s_pre tr2 tr2 )) (PreH2 : (t2_t <> 3)) (PreH3 : (repr_rel_node s_pre tr1_prev tr1 )) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2 tr2 ) ” 
  &&  “ (t2_t <> 3) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify1_partial_solve_wit_12 := atype_unify1_partial_solve_wit_12_pure -> atype_unify1_partial_solve_wit_12_aux.

Definition atype_unify1_which_implies_wit_1 := 
(
forall (tr2: TypeTree) (t2: Z) ,
  (store_type t2 tr2 )
|--
  EX (t2_t: Z) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
) \/
(
forall (tr2: TypeTree) (t2: Z) ,
  (store_type t2 tr2 )
|--
  EX (t2_t: Z) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
).

Definition atype_unify1_which_implies_wit_2 := 
(
forall (tr2: TypeTree) (t2: Z) (t2_t: Z) (PreH1 : (t2_t = 3)) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (n: Z) ,
  “ (t2_t = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ”
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
) \/
(
forall (tr2: TypeTree) (t2: Z) (t2_t: Z) (PreH1 : (t2_t = 3)) ,
  (store_type_aux t2 t2_t tr2 )
|--
  EX (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ”
  &&  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
).

Definition atype_unify1_which_implies_wit_3 := 
(
forall (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (t2: Z) (tp: Z) (PreH1 : (tp <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) ,
  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  EX (tr: TypeTree) ,
  “ (tr_opt = (Some (tr))) ” 
  &&  “ (solution_at s_pre n tr ) ”
  &&  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
) \/
(
forall (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (PreH1 : (tp <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) ,
  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  EX (tr: TypeTree) ,
  “ (tr_opt = (Some (tr))) ” 
  &&  “ (solution_at s_pre n tr ) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
).

Definition atype_unify1_which_implies_wit_4 := 
(
forall (tr2: TypeTree) (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t2: Z) (t2_t: Z) (PreH1 : (tp = 0)) (PreH2 : (t2_t = 3)) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  “ (tr_opt = None) ” 
  &&  “ (repr_rel_node s_pre tr2 tr2 ) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2 tr2 )
) \/
(
forall (tr2: TypeTree) (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t2: Z) (t2_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t2_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t2_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t2_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr2 = (TVar (n)))) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  “ (repr_rel_node s_pre tr2 tr2 ) ” 
  &&  “ (tr_opt = None) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2 tr2 )
).

Definition atype_unify1_which_implies_wit_4_split_goal_1 := 
forall (tr2: TypeTree) (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t2: Z) (t2_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t2_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t2_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t2_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr2 = (TVar (n)))) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  “ (repr_rel_node s_pre tr2 tr2 ) ”
.

Definition atype_unify1_which_implies_wit_4_split_goal_2 := 
forall (tr2: TypeTree) (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t2: Z) (t2_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t2_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t2_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t2_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr2 = (TVar (n)))) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  “ (tr_opt = None) ”
.

Definition atype_unify1_which_implies_wit_4_split_goal_spatial := 
forall (tr2: TypeTree) (s_pre: sol) (n: Z) (tr_opt: (@option TypeTree)) (tp: Z) (t2: Z) (t2_t: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (t2_t <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (t2_t >= INT_MIN)) (PreH5 : (tp = 0)) (PreH6 : (t2_t = 3)) (PreH7 : (0 <= n)) (PreH8 : (n < 100)) (PreH9 : (tr2 = (TVar (n)))) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution_aux ( &( "res" ) ) s_pre n tp tr_opt )
|--
  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2 tr2 )
.

Definition atype_unify1_which_implies_wit_5 := 
(
forall (tr2: TypeTree) (s_pre: sol) (t2: Z) (t2_t: Z) (PreH1 : (t2_t <> 3)) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (repr_rel_node s_pre tr2 tr2 ) ”
  &&  (store_type t2 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
) \/
(
forall (tr2: TypeTree) (s_pre: sol) (t2: Z) (t2_t: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (t2_t >= INT_MIN)) (PreH3 : (t2_t <> 3)) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  “ (repr_rel_node s_pre tr2 tr2 ) ”
  &&  (store_type t2 tr2 )
).

Definition atype_unify1_which_implies_wit_5_split_goal_1 := 
forall (tr2: TypeTree) (s_pre: sol) (t2: Z) (t2_t: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (t2_t >= INT_MIN)) (PreH3 : (t2_t <> 3)) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  “ (repr_rel_node s_pre tr2 tr2 ) ”
.

Definition atype_unify1_which_implies_wit_5_split_goal_spatial := 
forall (tr2: TypeTree) (t2: Z) (t2_t: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (t2_t >= INT_MIN)) (PreH3 : (t2_t <> 3)) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  (store_type t2 tr2 )
.

(*----- Function atype_unify2 -----*)

Definition atype_unify2_safety_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (PreH1 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH2 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify2_safety_wit_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1 = (TVar (n)))) (PreH5 : (t1_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH8 : (retval = 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_3 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1 = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval <> 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1 = (TVar (n)))) (PreH5 : (t1_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH8 : (retval <> 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_5 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (s_post: sol) (PreH1 : ((sol_update (s_pre) (n) (tr2)) = s_post)) (PreH2 : (retval = 0)) (PreH3 : (not_occur_final s_pre n tr2 )) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr1 = (TVar (n)))) (PreH7 : (t1_t = 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval = 0)) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t2_pre tr2 )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <> 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH3 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition atype_unify2_safety_wit_7 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (t1_t <> 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval = 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr1 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval <> 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_9 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (t1_t <> 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval <> 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (s_post: sol) (PreH1 : ((sol_update (s_pre) (n) (tr1)) = s_post)) (PreH2 : (retval = 0)) (PreH3 : (not_occur_final s_pre n tr1 )) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr2 = (TVar (n)))) (PreH7 : (t2_t = 3)) (PreH8 : (t1_t <> 3)) (PreH9 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH10 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH11 : (retval = 0)) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_11 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <> t2_t)) (PreH2 : (t2_t <> 3)) (PreH3 : (t1_t <> 3)) (PreH4 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH5 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition atype_unify2_safety_wit_12 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t = t2_t)) (PreH2 : (t2_t <> 3)) (PreH3 : (t1_t <> 3)) (PreH4 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH5 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition atype_unify2_safety_wit_13 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_from tr2_from s_pre s_post )) (PreH3 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH4 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH5 : (t2_t = 1)) (PreH6 : (t1_t = 1)) (PreH7 : (t1_t = t2_t)) (PreH8 : (t2_t <> 3)) (PreH9 : (t1_t <> 3)) (PreH10 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH11 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH3 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH4 : (t2_t = 1)) (PreH5 : (t1_t = 1)) (PreH6 : (t1_t = t2_t)) (PreH7 : (t2_t <> 3)) (PreH8 : (t1_t <> 3)) (PreH9 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH10 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_15 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (unify_rel tr1_from tr2_from s_pre s_post )) (PreH4 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH5 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH6 : (t2_t = 1)) (PreH7 : (t1_t = 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_16 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH4 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH5 : (t2_t = 1)) (PreH6 : (t1_t = 1)) (PreH7 : (t1_t = t2_t)) (PreH8 : (t2_t <> 3)) (PreH9 : (t1_t <> 3)) (PreH10 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH11 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_17 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <> 1)) (PreH2 : (t1_t = t2_t)) (PreH3 : (t2_t <> 3)) (PreH4 : (t1_t <> 3)) (PreH5 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH6 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition atype_unify2_safety_wit_18 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_tfn tr2_tfn s_pre s_post )) (PreH3 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH4 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH5 : (t2_t = 2)) (PreH6 : (t1_t = 2)) (PreH7 : (t1_t <> 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_19 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH3 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH4 : (t2_t = 2)) (PreH5 : (t1_t = 2)) (PreH6 : (t1_t <> 1)) (PreH7 : (t1_t = t2_t)) (PreH8 : (t2_t <> 3)) (PreH9 : (t1_t <> 3)) (PreH10 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH11 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_20 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (unify_rel tr1_tfn tr2_tfn s_pre s_post )) (PreH4 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH5 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH6 : (t2_t = 2)) (PreH7 : (t1_t = 2)) (PreH8 : (t1_t <> 1)) (PreH9 : (t1_t = t2_t)) (PreH10 : (t2_t <> 3)) (PreH11 : (t1_t <> 3)) (PreH12 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH13 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_21 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH4 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH5 : (t2_t = 2)) (PreH6 : (t1_t = 2)) (PreH7 : (t1_t <> 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((( &( "r" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ False ”
.

Definition atype_unify2_safety_wit_22 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (n = m)) (PreH2 : (t1_t = 0)) (PreH3 : (t1_t = 0)) (PreH4 : (tr1 = (TAtom (n)))) (PreH5 : (tr2 = (TAtom (m)))) (PreH6 : (t1_t <> 2)) (PreH7 : (t1_t <> 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition atype_unify2_safety_wit_23 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (n <> m)) (PreH2 : (t1_t = 0)) (PreH3 : (t1_t = 0)) (PreH4 : (tr1 = (TAtom (n)))) (PreH5 : (tr2 = (TAtom (m)))) (PreH6 : (t1_t <> 2)) (PreH7 : (t1_t <> 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition atype_unify2_entail_wit_1_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1 = (TVar (n)))) (PreH5 : (t1_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH8 : (retval = 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr2 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_1_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1 = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval = 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr2 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_2_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1 = (TVar (n)))) (PreH5 : (t1_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH8 : (retval <> 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_2_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1 = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval <> 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_3_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (t1_t <> 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval = 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr1 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_3_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr1 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval = 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr1 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_4_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (t1_t <> 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval <> 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_entail_wit_4_2 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr1 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval <> 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_return_wit_1 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (n <> m)) (PreH2 : (t1_t = 0)) (PreH3 : (t1_t = 0)) (PreH4 : (tr1 = (TAtom (n)))) (PreH5 : (tr2 = (TAtom (m)))) (PreH6 : (t1_t <> 2)) (PreH7 : (t1_t <> 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  EX (s_post_2: sol) ,
  “ (2 <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (m <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (t1_t <= INT_MAX)) (PreH4 : (m >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (t1_t >= INT_MIN)) (PreH7 : (n <> m)) (PreH8 : (t1_t = 0)) (PreH9 : (t1_t = 0)) (PreH10 : (tr1 = (TAtom (n)))) (PreH11 : (tr2 = (TAtom (m)))) (PreH12 : (t1_t <> 2)) (PreH13 : (t1_t <> 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_1_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (m <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (t1_t <= INT_MAX)) (PreH4 : (m >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (t1_t >= INT_MIN)) (PreH7 : (n <> m)) (PreH8 : (t1_t = 0)) (PreH9 : (t1_t = 0)) (PreH10 : (tr1 = (TAtom (n)))) (PreH11 : (tr2 = (TAtom (m)))) (PreH12 : (t1_t <> 2)) (PreH13 : (t1_t <> 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_2 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (n = m)) (PreH2 : (t1_t = 0)) (PreH3 : (t1_t = 0)) (PreH4 : (tr1 = (TAtom (n)))) (PreH5 : (tr2 = (TAtom (m)))) (PreH6 : (t1_t <> 2)) (PreH7 : (t1_t <> 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  EX (s_post: sol) ,
  “ (0 = 0) ” 
  &&  “ (unify_rel tr1_prev tr2_prev s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (m <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (t1_t <= INT_MAX)) (PreH4 : (m >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (t1_t >= INT_MIN)) (PreH7 : (n = m)) (PreH8 : (t1_t = 0)) (PreH9 : (t1_t = 0)) (PreH10 : (tr1 = (TAtom (n)))) (PreH11 : (tr2 = (TAtom (m)))) (PreH12 : (t1_t <> 2)) (PreH13 : (t1_t <> 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_pre ) ”
  &&  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_2_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (m <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (t1_t <= INT_MAX)) (PreH4 : (m >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (t1_t >= INT_MIN)) (PreH7 : (n = m)) (PreH8 : (t1_t = 0)) (PreH9 : (t1_t = 0)) (PreH10 : (tr1 = (TAtom (n)))) (PreH11 : (tr2 = (TAtom (m)))) (PreH12 : (t1_t <> 2)) (PreH13 : (t1_t <> 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_pre ) ”
.

Definition atype_unify2_return_wit_2_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (m: Z) (n: Z) (PreH1 : (m <= INT_MAX)) (PreH2 : (n <= INT_MAX)) (PreH3 : (t1_t <= INT_MAX)) (PreH4 : (m >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (t1_t >= INT_MIN)) (PreH7 : (n = m)) (PreH8 : (t1_t = 0)) (PreH9 : (t1_t = 0)) (PreH10 : (tr1 = (TAtom (n)))) (PreH11 : (tr2 = (TAtom (m)))) (PreH12 : (t1_t <> 2)) (PreH13 : (t1_t <> 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_3 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_rand tr2_rand s_post_3 s_post_4 )) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_2 = 0)) (PreH5 : (unify_rel tr1_tfn tr2_tfn s_pre s_post_3 )) (PreH6 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH7 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH8 : (t2_t = 2)) (PreH9 : (t1_t = 2)) (PreH10 : (t1_t <> 1)) (PreH11 : (t1_t = t2_t)) (PreH12 : (t2_t <> 3)) (PreH13 : (t1_t <> 3)) (PreH14 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH15 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post_4 )
  **  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_prev tr2_prev s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_rand tr2_rand s_post_3 s_post_4 )) (PreH7 : (retval_2 = 0)) (PreH8 : (retval_2 = 0)) (PreH9 : (unify_rel tr1_tfn tr2_tfn s_pre s_post_3 )) (PreH10 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH11 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH12 : (t2_t = 2)) (PreH13 : (t1_t = 2)) (PreH14 : (t1_t <> 1)) (PreH15 : (t1_t = t2_t)) (PreH16 : (t2_t <> 3)) (PreH17 : (t1_t <> 3)) (PreH18 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH19 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_4 ) ”
  &&  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_3_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_rand tr2_rand s_post_3 s_post_4 )) (PreH7 : (retval_2 = 0)) (PreH8 : (retval_2 = 0)) (PreH9 : (unify_rel tr1_tfn tr2_tfn s_pre s_post_3 )) (PreH10 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH11 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH12 : (t2_t = 2)) (PreH13 : (t1_t = 2)) (PreH14 : (t1_t <> 1)) (PreH15 : (t1_t = t2_t)) (PreH16 : (t2_t <> 3)) (PreH17 : (t1_t <> 3)) (PreH18 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH19 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_4 ) ”
.

Definition atype_unify2_return_wit_3_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_rand tr2_rand s_post_3 s_post_4 )) (PreH7 : (retval_2 = 0)) (PreH8 : (retval_2 = 0)) (PreH9 : (unify_rel tr1_tfn tr2_tfn s_pre s_post_3 )) (PreH10 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH11 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH12 : (t2_t = 2)) (PreH13 : (t1_t = 2)) (PreH14 : (t1_t <> 1)) (PreH15 : (t1_t = t2_t)) (PreH16 : (t2_t <> 3)) (PreH17 : (t1_t <> 3)) (PreH18 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH19 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_4 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (unify_rel tr1_tfn tr2_tfn s_pre s_post_3 )) (PreH5 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH6 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH7 : (t2_t = 2)) (PreH8 : (t1_t = 2)) (PreH9 : (t1_t <> 1)) (PreH10 : (t1_t = t2_t)) (PreH11 : (t2_t <> 3)) (PreH12 : (t1_t <> 3)) (PreH13 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH14 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post_4 )
  **  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval_2: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (retval_2 = 0)) (PreH8 : (unify_rel tr1_tfn tr2_tfn s_pre s_post_3 )) (PreH9 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH10 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH11 : (t2_t = 2)) (PreH12 : (t1_t = 2)) (PreH13 : (t1_t <> 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_4_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval_2: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (retval_2 = 0)) (PreH8 : (unify_rel tr1_tfn tr2_tfn s_pre s_post_3 )) (PreH9 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH10 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH11 : (t2_t = 2)) (PreH12 : (t1_t = 2)) (PreH13 : (t1_t <> 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_5 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH4 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH5 : (t2_t = 2)) (PreH6 : (t1_t = 2)) (PreH7 : (t1_t <> 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH8 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH9 : (t2_t = 2)) (PreH10 : (t1_t = 2)) (PreH11 : (t1_t <> 1)) (PreH12 : (t1_t = t2_t)) (PreH13 : (t2_t <> 3)) (PreH14 : (t1_t <> 3)) (PreH15 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH16 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_5_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (2 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (2 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH8 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH9 : (t2_t = 2)) (PreH10 : (t1_t = 2)) (PreH11 : (t1_t <> 1)) (PreH12 : (t1_t = t2_t)) (PreH13 : (t2_t <> 3)) (PreH14 : (t1_t <> 3)) (PreH15 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH16 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_6 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (unify_rel tr1_to tr2_to s_post_3 s_post_4 )) (PreH3 : (retval_2 = 0)) (PreH4 : (retval_2 = 0)) (PreH5 : (unify_rel tr1_from tr2_from s_pre s_post_3 )) (PreH6 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH7 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH8 : (t2_t = 1)) (PreH9 : (t1_t = 1)) (PreH10 : (t1_t = t2_t)) (PreH11 : (t2_t <> 3)) (PreH12 : (t1_t <> 3)) (PreH13 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH14 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post_4 )
  **  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  EX (s_post: sol) ,
  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_prev tr2_prev s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_to tr2_to s_post_3 s_post_4 )) (PreH7 : (retval_2 = 0)) (PreH8 : (retval_2 = 0)) (PreH9 : (unify_rel tr1_from tr2_from s_pre s_post_3 )) (PreH10 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH11 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH12 : (t2_t = 1)) (PreH13 : (t1_t = 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_4 ) ”
  &&  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_6_split_goal_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_to tr2_to s_post_3 s_post_4 )) (PreH7 : (retval_2 = 0)) (PreH8 : (retval_2 = 0)) (PreH9 : (unify_rel tr1_from tr2_from s_pre s_post_3 )) (PreH10 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH11 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH12 : (t2_t = 1)) (PreH13 : (t1_t = 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_4 ) ”
.

Definition atype_unify2_return_wit_6_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval = 0)) (PreH6 : (unify_rel tr1_to tr2_to s_post_3 s_post_4 )) (PreH7 : (retval_2 = 0)) (PreH8 : (retval_2 = 0)) (PreH9 : (unify_rel tr1_from tr2_from s_pre s_post_3 )) (PreH10 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH11 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH12 : (t2_t = 1)) (PreH13 : (t1_t = 1)) (PreH14 : (t1_t = t2_t)) (PreH15 : (t2_t <> 3)) (PreH16 : (t1_t <> 3)) (PreH17 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH18 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_7 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval_2: Z) (s_post_4: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval_2 = 0)) (PreH4 : (unify_rel tr1_from tr2_from s_pre s_post_3 )) (PreH5 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH6 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH7 : (t2_t = 1)) (PreH8 : (t1_t = 1)) (PreH9 : (t1_t = t2_t)) (PreH10 : (t2_t <> 3)) (PreH11 : (t1_t <> 3)) (PreH12 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH13 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post_4 )
  **  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval_2: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (retval_2 = 0)) (PreH8 : (unify_rel tr1_from tr2_from s_pre s_post_3 )) (PreH9 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH10 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH11 : (t2_t = 1)) (PreH12 : (t1_t = 1)) (PreH13 : (t1_t = t2_t)) (PreH14 : (t2_t <> 3)) (PreH15 : (t1_t <> 3)) (PreH16 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH17 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_7_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval_2: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (retval_2 = 0)) (PreH8 : (unify_rel tr1_from tr2_from s_pre s_post_3 )) (PreH9 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH10 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH11 : (t2_t = 1)) (PreH12 : (t1_t = 1)) (PreH13 : (t1_t = t2_t)) (PreH14 : (t2_t <> 3)) (PreH15 : (t1_t <> 3)) (PreH16 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH17 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_8 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post_3: sol) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH4 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH5 : (t2_t = 1)) (PreH6 : (t1_t = 1)) (PreH7 : (t1_t = t2_t)) (PreH8 : (t2_t <> 3)) (PreH9 : (t1_t <> 3)) (PreH10 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH11 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  EX (s_post_2: sol) ,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH8 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH9 : (t2_t = 1)) (PreH10 : (t1_t = 1)) (PreH11 : (t1_t = t2_t)) (PreH12 : (t2_t <> 3)) (PreH13 : (t1_t <> 3)) (PreH14 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH15 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_8_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (retval: Z) (PreH1 : (t2_t <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (t2_t >= INT_MIN)) (PreH4 : (1 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH8 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH9 : (t2_t = 1)) (PreH10 : (t1_t = 1)) (PreH11 : (t1_t = t2_t)) (PreH12 : (t2_t <> 3)) (PreH13 : (t1_t <> 3)) (PreH14 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH15 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_9 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <> t2_t)) (PreH2 : (t2_t <> 3)) (PreH3 : (t1_t <> 3)) (PreH4 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH5 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  EX (s_post_2: sol) ,
  “ (2 <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <= INT_MAX)) (PreH2 : (t2_t <= INT_MAX)) (PreH3 : (t1_t >= INT_MIN)) (PreH4 : (t2_t >= INT_MIN)) (PreH5 : (t1_t <> t2_t)) (PreH6 : (t2_t <> 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_9_split_goal_spatial := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <= INT_MAX)) (PreH2 : (t2_t <= INT_MAX)) (PreH3 : (t1_t >= INT_MIN)) (PreH4 : (t2_t >= INT_MIN)) (PreH5 : (t1_t <> t2_t)) (PreH6 : (t2_t <> 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
|--
  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_10 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : ((sol_update (s_pre) (n) (tr1)) = s_post_3)) (PreH2 : (retval = 0)) (PreH3 : (not_occur_final s_pre n tr1 )) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr2 = (TVar (n)))) (PreH7 : (t2_t = 3)) (PreH8 : (t1_t <> 3)) (PreH9 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH10 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH11 : (retval = 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  EX (s_post: sol) ,
  “ (0 = 0) ” 
  &&  “ (unify_rel tr1_prev tr2_prev s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : ((sol_update (s_pre) (n) (tr1)) = s_post_3)) (PreH6 : (retval = 0)) (PreH7 : (not_occur_final s_pre n tr1 )) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr2 = (TVar (n)))) (PreH11 : (t2_t = 3)) (PreH12 : (t1_t <> 3)) (PreH13 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH14 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH15 : (retval = 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_3 ) ”
  &&  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_10_split_goal_1 := 
forall (t2_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : ((sol_update (s_pre) (n) (tr1)) = s_post_3)) (PreH6 : (retval = 0)) (PreH7 : (not_occur_final s_pre n tr1 )) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr2 = (TVar (n)))) (PreH11 : (t2_t = 3)) (PreH12 : (t1_t <> 3)) (PreH13 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH14 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH15 : (retval = 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_3 ) ”
.

Definition atype_unify2_return_wit_10_split_goal_spatial := 
forall (t2_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : ((sol_update (s_pre) (n) (tr1)) = s_post_3)) (PreH6 : (retval = 0)) (PreH7 : (not_occur_final s_pre n tr1 )) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr2 = (TVar (n)))) (PreH11 : (t2_t = 3)) (PreH12 : (t1_t <> 3)) (PreH13 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH14 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH15 : (retval = 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_11 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (t1_t <> 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval <> 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  EX (s_post_2: sol) ,
  “ (1 <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t2_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= n)) (PreH7 : (n < 100)) (PreH8 : (tr2 = (TVar (n)))) (PreH9 : (t2_t = 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH13 : (retval <> 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (store_type t2_pre tr2 )
).

Definition atype_unify2_return_wit_11_split_goal_spatial := 
forall (t2_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= n)) (PreH7 : (n < 100)) (PreH8 : (tr2 = (TVar (n)))) (PreH9 : (t2_t = 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH13 : (retval <> 0)) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (store_type t2_pre tr2 )
.

Definition atype_unify2_return_wit_12 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : ((sol_update (s_pre) (n) (tr2)) = s_post_3)) (PreH2 : (retval = 0)) (PreH3 : (not_occur_final s_pre n tr2 )) (PreH4 : (0 <= n)) (PreH5 : (n < 100)) (PreH6 : (tr1 = (TVar (n)))) (PreH7 : (t1_t = 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval = 0)) ,
  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  EX (s_post: sol) ,
  “ (0 = 0) ” 
  &&  “ (unify_rel tr1_prev tr2_prev s_pre s_post ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : ((sol_update (s_pre) (n) (tr2)) = s_post_3)) (PreH6 : (retval = 0)) (PreH7 : (not_occur_final s_pre n tr2 )) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr1 = (TVar (n)))) (PreH11 : (t1_t = 3)) (PreH12 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH13 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH14 : (retval = 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_3 ) ”
  &&  (store_type t1_pre tr1 )
).

Definition atype_unify2_return_wit_12_split_goal_1 := 
forall (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : ((sol_update (s_pre) (n) (tr2)) = s_post_3)) (PreH6 : (retval = 0)) (PreH7 : (not_occur_final s_pre n tr2 )) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr1 = (TVar (n)))) (PreH11 : (t1_t = 3)) (PreH12 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH13 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH14 : (retval = 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (unify_rel tr1_prev tr2_prev s_pre s_post_3 ) ”
.

Definition atype_unify2_return_wit_12_split_goal_spatial := 
forall (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (s_post_3: sol) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : ((sol_update (s_pre) (n) (tr2)) = s_post_3)) (PreH6 : (retval = 0)) (PreH7 : (not_occur_final s_pre n tr2 )) (PreH8 : (0 <= n)) (PreH9 : (n < 100)) (PreH10 : (tr1 = (TVar (n)))) (PreH11 : (t1_t = 3)) (PreH12 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH13 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH14 : (retval = 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (store_type t1_pre tr1 )
.

Definition atype_unify2_return_wit_13 := 
(
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1 = (TVar (n)))) (PreH5 : (t1_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH8 : (retval <> 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  EX (s_post_2: sol) ,
  “ (1 <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
) \/
(
forall (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= n)) (PreH7 : (n < 100)) (PreH8 : (tr1 = (TVar (n)))) (PreH9 : (t1_t = 3)) (PreH10 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH11 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH12 : (retval <> 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (store_type t1_pre tr1 )
).

Definition atype_unify2_return_wit_13_split_goal_spatial := 
forall (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (n <= INT_MAX)) (PreH2 : (3 <= INT_MAX)) (PreH3 : (n >= INT_MIN)) (PreH4 : (3 >= INT_MIN)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= n)) (PreH7 : (n < 100)) (PreH8 : (tr1 = (TVar (n)))) (PreH9 : (t1_t = 3)) (PreH10 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH11 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH12 : (retval <> 0)) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  (store_type t1_pre tr1 )
.

Definition atype_unify2_partial_solve_wit_1 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (PreH1 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH2 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  (store_type t2_pre tr2 )
|--
  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_partial_solve_wit_2_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (PreH1 : (t1_t = 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH3 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  “ (3 = 3) ”
.

Definition atype_unify2_partial_solve_wit_2_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (PreH1 : (t1_t = 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH3 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  “ (3 = 3) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t1_pre 3 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
.

Definition atype_unify2_partial_solve_wit_2 := atype_unify2_partial_solve_wit_2_pure -> atype_unify2_partial_solve_wit_2_aux.

Definition atype_unify2_partial_solve_wit_3_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (PreH1 : (3 = 3)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1 = (TVar (n)))) (PreH5 : (t1_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "occur" ) )) # Int  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ”
.

Definition atype_unify2_partial_solve_wit_3_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (PreH1 : (3 = 3)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr1 = (TVar (n)))) (PreH5 : (t1_t = 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_3 := atype_unify2_partial_solve_wit_3_pure -> atype_unify2_partial_solve_wit_3_aux.

Definition atype_unify2_partial_solve_wit_4 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1 = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval = 0)) ,
  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr2 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type t2_pre tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_5_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1 = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval = 0)) ,
  (store_type t2_pre tr2 )
  **  (store_type retval_2 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (not_occur_final s_pre n tr2 ) ”
.

Definition atype_unify2_partial_solve_wit_5_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr2 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr1 = (TVar (n)))) (PreH6 : (t1_t = 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH9 : (retval = 0)) ,
  (store_type t2_pre tr2 )
  **  (store_type retval_2 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (not_occur_final s_pre n tr2 ) ” 
  &&  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr2 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ” 
  &&  “ (t1_t = 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type retval_2 tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_5 := atype_unify2_partial_solve_wit_5_pure -> atype_unify2_partial_solve_wit_5_aux.

Definition atype_unify2_partial_solve_wit_6 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (PreH1 : (t1_t <> 3)) (PreH2 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH3 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t2_pre tr2 )
|--
  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_type t2_pre tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_7_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t2_t = 3)) (PreH2 : (t1_t <> 3)) (PreH3 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH4 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (3 = 3) ”
.

Definition atype_unify2_partial_solve_wit_7_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t2_t = 3)) (PreH2 : (t1_t <> 3)) (PreH3 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH4 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (3 = 3) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  (store_type_aux t2_pre 3 tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_7 := atype_unify2_partial_solve_wit_7_pure -> atype_unify2_partial_solve_wit_7_aux.

Definition atype_unify2_partial_solve_wit_8 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (PreH1 : (3 = 3)) (PreH2 : (0 <= n)) (PreH3 : (n < 100)) (PreH4 : (tr2 = (TVar (n)))) (PreH5 : (t2_t = 3)) (PreH6 : (t1_t <> 3)) (PreH7 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH8 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_9_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr2 = (TVar (n)))) (PreH4 : (t2_t = 3)) (PreH5 : (t1_t <> 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "occur" ) )) # Int  |->_)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  (store_type t1_pre tr1 )
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ”
.

Definition atype_unify2_partial_solve_wit_9_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (PreH1 : (0 <= n)) (PreH2 : (n < 100)) (PreH3 : (tr2 = (TVar (n)))) (PreH4 : (t2_t = 3)) (PreH5 : (t1_t <> 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_9 := atype_unify2_partial_solve_wit_9_pure -> atype_unify2_partial_solve_wit_9_aux.

Definition atype_unify2_partial_solve_wit_10 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr1 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval = 0)) ,
  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr1 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type t1_pre tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_11_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr1 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval = 0)) ,
  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((( &( "occur" ) )) # Int  |-> retval)
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (not_occur_final s_pre n tr1 ) ”
.

Definition atype_unify2_partial_solve_wit_11_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (n: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = 0)) (PreH2 : (not_occur_final s_pre n tr1 )) (PreH3 : (0 <= n)) (PreH4 : (n < 100)) (PreH5 : (tr2 = (TVar (n)))) (PreH6 : (t2_t = 3)) (PreH7 : (t1_t <> 3)) (PreH8 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH9 : (repr_rel_node s_pre tr2_prev tr2 )) (PreH10 : (retval = 0)) ,
  (store_type t1_pre tr1 )
  **  (store_type retval_2 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
|--
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (not_occur_final s_pre n tr1 ) ” 
  &&  “ (retval = 0) ” 
  &&  “ (not_occur_final s_pre n tr1 ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ” 
  &&  “ (t2_t = 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ” 
  &&  “ (retval = 0) ”
  &&  (store_type retval_2 tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_pre tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> 3)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
.

Definition atype_unify2_partial_solve_wit_11 := atype_unify2_partial_solve_wit_11_pure -> atype_unify2_partial_solve_wit_11_aux.

Definition atype_unify2_partial_solve_wit_12_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t = 1)) (PreH2 : (t1_t = t2_t)) (PreH3 : (t2_t <> 3)) (PreH4 : (t1_t <> 3)) (PreH5 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH6 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (1 = 1) ” 
  &&  “ (1 = t2_t) ”
.

Definition atype_unify2_partial_solve_wit_12_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t = 1)) (PreH2 : (t1_t = t2_t)) (PreH3 : (t2_t <> 3)) (PreH4 : (t1_t <> 3)) (PreH5 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH6 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (1 = 1) ” 
  &&  “ (1 = t2_t) ” 
  &&  “ (t1_t = 1) ” 
  &&  “ (t1_t = t2_t) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1_pre 1 tr1 )
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_12 := atype_unify2_partial_solve_wit_12_pure -> atype_unify2_partial_solve_wit_12_aux.

Definition atype_unify2_partial_solve_wit_13 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (PreH1 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH2 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH3 : (1 = 1)) (PreH4 : (t2_t = 1)) (PreH5 : (t1_t = 1)) (PreH6 : (t1_t = t2_t)) (PreH7 : (t2_t <> 3)) (PreH8 : (t1_t <> 3)) (PreH9 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH10 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  (store_type t1_from tr1_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  (store_type t2_from tr2_from )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (tr1 = (TArrow (tr1_from) (tr1_to))) ” 
  &&  “ (tr2 = (TArrow (tr2_from) (tr2_to))) ” 
  &&  “ (t2_t = 1) ” 
  &&  “ (t1_t = 1) ” 
  &&  “ (t1_t = t2_t) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_14 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_to: TypeTree) (t2_to: Z) (tr2_from: TypeTree) (t2_from: Z) (tr1_to: TypeTree) (t1_to: Z) (tr1_from: TypeTree) (t1_from: Z) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (unify_rel tr1_from tr2_from s_pre s_post )) (PreH4 : (tr1 = (TArrow (tr1_from) (tr1_to)))) (PreH5 : (tr2 = (TArrow (tr2_from) (tr2_to)))) (PreH6 : (t2_t = 1)) (PreH7 : (t1_t = 1)) (PreH8 : (t1_t = t2_t)) (PreH9 : (t2_t <> 3)) (PreH10 : (t1_t <> 3)) (PreH11 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH12 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_from tr2_from s_pre s_post ) ” 
  &&  “ (tr1 = (TArrow (tr1_from) (tr1_to))) ” 
  &&  “ (tr2 = (TArrow (tr2_from) (tr2_to))) ” 
  &&  “ (t2_t = 1) ” 
  &&  “ (t1_t = 1) ” 
  &&  “ (t1_t = t2_t) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_to tr1_to )
  **  (store_type t2_to tr2_to )
  **  (store_type t1_from tr1_from )
  **  (store_type t2_from tr2_from )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 1)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_15_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t = 2)) (PreH2 : (t1_t <> 1)) (PreH3 : (t1_t = t2_t)) (PreH4 : (t2_t <> 3)) (PreH5 : (t1_t <> 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (2 = 2) ” 
  &&  “ (2 = t2_t) ”
.

Definition atype_unify2_partial_solve_wit_15_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t = 2)) (PreH2 : (t1_t <> 1)) (PreH3 : (t1_t = t2_t)) (PreH4 : (t2_t <> 3)) (PreH5 : (t1_t <> 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (2 = 2) ” 
  &&  “ (2 = t2_t) ” 
  &&  “ (t1_t = 2) ” 
  &&  “ (t1_t <> 1) ” 
  &&  “ (t1_t = t2_t) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1_pre 2 tr1 )
  **  (store_type_aux t2_pre t2_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_15 := atype_unify2_partial_solve_wit_15_pure -> atype_unify2_partial_solve_wit_15_aux.

Definition atype_unify2_partial_solve_wit_16 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (PreH1 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH2 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH3 : (2 = 2)) (PreH4 : (t2_t = 2)) (PreH5 : (t1_t = 2)) (PreH6 : (t1_t <> 1)) (PreH7 : (t1_t = t2_t)) (PreH8 : (t2_t <> 3)) (PreH9 : (t1_t <> 3)) (PreH10 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH11 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  (store_type t1_tfn tr1_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (tr1 = (TApply (tr1_tfn) (tr1_rand))) ” 
  &&  “ (tr2 = (TApply (tr2_tfn) (tr2_rand))) ” 
  &&  “ (t2_t = 2) ” 
  &&  “ (t1_t = 2) ” 
  &&  “ (t1_t <> 1) ” 
  &&  “ (t1_t = t2_t) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_solution ( &( "res" ) ) s_pre )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_17 := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (tr2_rand: TypeTree) (t2_rand: Z) (tr2_tfn: TypeTree) (t2_tfn: Z) (tr1_rand: TypeTree) (t1_rand: Z) (tr1_tfn: TypeTree) (t1_tfn: Z) (s_post: sol) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (unify_rel tr1_tfn tr2_tfn s_pre s_post )) (PreH4 : (tr1 = (TApply (tr1_tfn) (tr1_rand)))) (PreH5 : (tr2 = (TApply (tr2_tfn) (tr2_rand)))) (PreH6 : (t2_t = 2)) (PreH7 : (t1_t = 2)) (PreH8 : (t1_t <> 1)) (PreH9 : (t1_t = t2_t)) (PreH10 : (t2_t <> 3)) (PreH11 : (t1_t <> 3)) (PreH12 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH13 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
|--
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (unify_rel tr1_tfn tr2_tfn s_pre s_post ) ” 
  &&  “ (tr1 = (TApply (tr1_tfn) (tr1_rand))) ” 
  &&  “ (tr2 = (TApply (tr2_tfn) (tr2_rand))) ” 
  &&  “ (t2_t = 2) ” 
  &&  “ (t1_t = 2) ” 
  &&  “ (t1_t <> 1) ” 
  &&  “ (t1_t = t2_t) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  (store_solution ( &( "res" ) ) s_post )
  **  (store_type t1_rand tr1_rand )
  **  (store_type t2_rand tr2_rand )
  **  (store_type t1_tfn tr1_tfn )
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  ((&((t1_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  ((&((t2_pre)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> 2)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
.

Definition atype_unify2_partial_solve_wit_18_pure := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <> 2)) (PreH2 : (t1_t <> 1)) (PreH3 : (t1_t = t2_t)) (PreH4 : (t2_t <> 3)) (PreH5 : (t1_t <> 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((( &( "t2" ) )) # Ptr  |-> t2_pre)
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((( &( "t1" ) )) # Ptr  |-> t1_pre)
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (t1_t = t1_t) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (t1_t <> 1) ” 
  &&  “ (t1_t <> 2) ”
.

Definition atype_unify2_partial_solve_wit_18_aux := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_prev: TypeTree) (tr1_prev: TypeTree) (tr2: TypeTree) (tr1: TypeTree) (s_pre: sol) (t1_t: Z) (t2_t: Z) (PreH1 : (t1_t <> 2)) (PreH2 : (t1_t <> 1)) (PreH3 : (t1_t = t2_t)) (PreH4 : (t2_t <> 3)) (PreH5 : (t1_t <> 3)) (PreH6 : (repr_rel_node s_pre tr1_prev tr1 )) (PreH7 : (repr_rel_node s_pre tr2_prev tr2 )) ,
  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2_pre t2_t tr2 )
  **  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  (store_solution ( &( "res" ) ) s_pre )
|--
  “ (t1_t = t1_t) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (t1_t <> 1) ” 
  &&  “ (t1_t <> 2) ” 
  &&  “ (t1_t <> 2) ” 
  &&  “ (t1_t <> 1) ” 
  &&  “ (t1_t = t2_t) ” 
  &&  “ (t2_t <> 3) ” 
  &&  “ (t1_t <> 3) ” 
  &&  “ (repr_rel_node s_pre tr1_prev tr1 ) ” 
  &&  “ (repr_rel_node s_pre tr2_prev tr2 ) ”
  &&  ((&((t1_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1_pre t1_t tr1 )
  **  ((&((t2_pre)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t2_pre t1_t tr2 )
  **  (store_solution ( &( "res" ) ) s_pre )
.

Definition atype_unify2_partial_solve_wit_18 := atype_unify2_partial_solve_wit_18_pure -> atype_unify2_partial_solve_wit_18_aux.

Definition atype_unify2_which_implies_wit_1 := 
(
forall (tr1: TypeTree) (t1: Z) ,
  (store_type t1 tr1 )
|--
  EX (t1_t: Z) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
) \/
(
forall (tr1: TypeTree) (t1: Z) ,
  (store_type t1 tr1 )
|--
  EX (t1_t: Z) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
).

Definition atype_unify2_which_implies_wit_2 := 
(
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) (PreH1 : (t1_t = 3)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
|--
  EX (n: Z) ,
  “ (t1_t = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ”
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
) \/
(
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) (PreH1 : (t1_t = 3)) ,
  (store_type_aux t1 t1_t tr1 )
|--
  EX (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr1 = (TVar (n))) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
).

Definition atype_unify2_which_implies_wit_3 := 
(
forall (tr2: TypeTree) (t2: Z) ,
  (store_type t2 tr2 )
|--
  EX (t2_t: Z) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
) \/
(
forall (tr2: TypeTree) (t2: Z) ,
  (store_type t2 tr2 )
|--
  EX (t2_t: Z) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
).

Definition atype_unify2_which_implies_wit_4 := 
(
forall (tr2: TypeTree) (t2: Z) (t2_t: Z) (PreH1 : (t2_t = 3)) ,
  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (n: Z) ,
  “ (t2_t = 3) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ”
  &&  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
) \/
(
forall (tr2: TypeTree) (t2: Z) (t2_t: Z) (PreH1 : (t2_t = 3)) ,
  (store_type_aux t2 t2_t tr2 )
|--
  EX (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n < 100) ” 
  &&  “ (tr2 = (TVar (n))) ”
  &&  ((&((t2)  # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name")) # Int  |-> n)
).

Definition atype_unify2_which_implies_wit_5 := 
(
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
|--
  (store_type t1 tr1 )
) \/
(
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) (PreH1 : (t1_t <= INT_MAX)) (PreH2 : (t1_t >= INT_MIN)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
|--
  (store_type t1 tr1 )
).

Definition atype_unify2_which_implies_wit_5_split_goal_spatial := 
forall (tr1: TypeTree) (t1: Z) (t1_t: Z) (PreH1 : (t1_t <= INT_MAX)) (PreH2 : (t1_t >= INT_MIN)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
|--
  (store_type t1 tr1 )
.

Definition atype_unify2_which_implies_wit_6 := 
(
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) (PreH1 : (t1_t = 1)) (PreH2 : (t1_t = t2_t)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1 t1_t tr1 )
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (tr2_to: TypeTree)  (t2_to: Z)  (tr2_from: TypeTree)  (t2_from: Z)  (tr1_to: TypeTree)  (t1_to: Z)  (tr1_from: TypeTree)  (t1_from: Z) ,
  “ (tr1 = (TArrow (tr1_from) (tr1_to))) ” 
  &&  “ (tr2 = (TArrow (tr2_from) (tr2_to))) ” 
  &&  “ (t1_t = 1) ” 
  &&  “ (t2_t = 1) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  (store_type t1_from tr1_from )
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  (store_type t2_from tr2_from )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
  **  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) (PreH1 : (t1_t = 1)) (PreH2 : (t1_t = t2_t)) ,
  (store_type_aux t1 t1_t tr1 )
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (tr2_to: TypeTree)  (t2_to: Z)  (tr2_from: TypeTree)  (t2_from: Z)  (tr1_to: TypeTree)  (t1_to: Z)  (tr1_from: TypeTree)  (t1_from: Z) ,
  “ (tr1 = (TArrow (tr1_from) (tr1_to))) ” 
  &&  “ (tr2 = (TArrow (tr2_from) (tr2_to))) ” 
  &&  “ (t2_t = 1) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t1_from)
  **  (store_type t1_from tr1_from )
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t1_to)
  **  (store_type t1_to tr1_to )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from")) # Ptr  |-> t2_from)
  **  (store_type t2_from tr2_from )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to")) # Ptr  |-> t2_to)
  **  (store_type t2_to tr2_to )
).

Definition atype_unify2_which_implies_wit_7 := 
(
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) (PreH1 : (t1_t = 2)) (PreH2 : (t1_t = t2_t)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t1 t1_t tr1 )
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (tr2_rand: TypeTree)  (t2_rand: Z)  (tr2_tfn: TypeTree)  (t2_tfn: Z)  (tr1_rand: TypeTree)  (t1_rand: Z)  (tr1_tfn: TypeTree)  (t1_tfn: Z) ,
  “ (tr1 = (TApply (tr1_tfn) (tr1_rand))) ” 
  &&  “ (tr2 = (TApply (tr2_tfn) (tr2_rand))) ” 
  &&  “ (t1_t = 2) ” 
  &&  “ (t2_t = 2) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  (store_type t1_tfn tr1_tfn )
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
  **  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) (PreH1 : (t1_t = 2)) (PreH2 : (t1_t = t2_t)) ,
  (store_type_aux t1 t1_t tr1 )
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (tr2_rand: TypeTree)  (t2_rand: Z)  (tr2_tfn: TypeTree)  (t2_tfn: Z)  (tr1_rand: TypeTree)  (t1_rand: Z)  (tr1_tfn: TypeTree)  (t1_tfn: Z) ,
  “ (tr1 = (TApply (tr1_tfn) (tr1_rand))) ” 
  &&  “ (tr2 = (TApply (tr2_tfn) (tr2_rand))) ” 
  &&  “ (t2_t = 2) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t1_tfn)
  **  (store_type t1_tfn tr1_tfn )
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t1_rand)
  **  (store_type t1_rand tr1_rand )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn")) # Ptr  |-> t2_tfn)
  **  (store_type t2_tfn tr2_tfn )
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand")) # Ptr  |-> t2_rand)
  **  (store_type t2_rand tr2_rand )
).

Definition atype_unify2_which_implies_wit_8 := 
(
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) (PreH1 : (t1_t = t2_t)) (PreH2 : (t1_t <> 3)) (PreH3 : (t1_t <> 1)) (PreH4 : (t1_t <> 2)) ,
  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  (store_type_aux t1 t1_t tr1 )
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (m: Z)  (n: Z) ,
  “ (t1_t = 0) ” 
  &&  “ (t2_t = 0) ” 
  &&  “ (tr1 = (TAtom (n))) ” 
  &&  “ (tr2 = (TAtom (m))) ”
  &&  ((&((t1)  # "atype" ->ₛ "t")) # Int  |-> t1_t)
  **  ((&((t2)  # "atype" ->ₛ "t")) # Int  |-> t2_t)
  **  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
) \/
(
forall (tr2: TypeTree) (tr1: TypeTree) (t1: Z) (t1_t: Z) (t2: Z) (t2_t: Z) (PreH1 : (t1_t = t2_t)) (PreH2 : (t1_t <> 3)) (PreH3 : (t1_t <> 1)) (PreH4 : (t1_t <> 2)) ,
  (store_type_aux t1 t1_t tr1 )
  **  (store_type_aux t2 t2_t tr2 )
|--
  EX (m: Z)  (n: Z) ,
  “ (t1_t = 0) ” 
  &&  “ (t2_t = 0) ” 
  &&  “ (tr1 = (TAtom (n))) ” 
  &&  “ (tr2 = (TAtom (m))) ”
  &&  ((&((t1)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> n)
  **  ((&((t2)  # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name")) # Int  |-> m)
).

Definition atype_unify_derive_final_by_verify := 
forall (t2_pre: Z) (t1_pre: Z) (tr2_final: TypeTree) (tr1_final: TypeTree) (s_pre_final: sol) ,
  (store_compressed_solution ( &( "res" ) ) s_pre_final )
  **  (store_type t1_pre tr1_final )
  **  (store_type t2_pre tr2_final )
|--
EX (s_pre_verify: sol) (tr1_verify: TypeTree) (tr2_verify: TypeTree) ,
  ((store_solution ( &( "res" ) ) s_pre_verify )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify ))
  **
  (((EX s_post_3 retval_2,
  “ (retval_2 = 0) ” 
  &&  “ (unify_rel tr1_verify tr2_verify s_pre_verify s_post_3 ) ”
  &&  (store_solution ( &( "res" ) ) s_post_3 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify ))
  ||
  (EX s_post_4 retval_2,
  “ (retval_2 <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_4 )
  **  (store_type t1_pre tr1_verify )
  **  (store_type t2_pre tr2_verify )))
  -*
  ((EX s_post retval,
  “ (retval = 0) ” 
  &&  “ (sol_correct_iter tr1_final tr2_final s_pre_final s_post ) ”
  &&  (store_compressed_solution ( &( "res" ) ) s_post )
  **  (store_type t1_pre tr1_final )
  **  (store_type t2_pre tr2_final ))
  ||
  (EX s_post_2 retval,
  “ (retval <> 0) ”
  &&  (store_solution ( &( "res" ) ) s_post_2 )
  **  (store_type t1_pre tr1_final )
  **  (store_type t2_pre tr2_final ))))
.

Module Type VC_Correct.

Include typeinfer_Strategy_Correct.

Axiom proof_of_atype_unify_safety_wit_1 : atype_unify_safety_wit_1.
Axiom proof_of_atype_unify_return_wit_1 : atype_unify_return_wit_1.
Axiom proof_of_atype_unify_return_wit_2 : atype_unify_return_wit_2.
Axiom proof_of_atype_unify_return_wit_3 : atype_unify_return_wit_3.
Axiom proof_of_atype_unify_return_wit_4 : atype_unify_return_wit_4.
Axiom proof_of_atype_unify_return_wit_5 : atype_unify_return_wit_5.
Axiom proof_of_atype_unify_return_wit_6 : atype_unify_return_wit_6.
Axiom proof_of_atype_unify_partial_solve_wit_1 : atype_unify_partial_solve_wit_1.
Axiom proof_of_atype_unify_partial_solve_wit_2_pure : atype_unify_partial_solve_wit_2_pure.
Axiom proof_of_atype_unify_partial_solve_wit_2 : atype_unify_partial_solve_wit_2.
Axiom proof_of_atype_unify_partial_solve_wit_3_pure : atype_unify_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify_partial_solve_wit_3 : atype_unify_partial_solve_wit_3.
Axiom proof_of_atype_unify_partial_solve_wit_4_pure : atype_unify_partial_solve_wit_4_pure.
Axiom proof_of_atype_unify_partial_solve_wit_4 : atype_unify_partial_solve_wit_4.
Axiom proof_of_atype_unify_partial_solve_wit_5_pure : atype_unify_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify_partial_solve_wit_5 : atype_unify_partial_solve_wit_5.
Axiom proof_of_atype_unify_partial_solve_wit_6_pure : atype_unify_partial_solve_wit_6_pure.
Axiom proof_of_atype_unify_partial_solve_wit_6 : atype_unify_partial_solve_wit_6.
Axiom proof_of_atype_unify_partial_solve_wit_7 : atype_unify_partial_solve_wit_7.
Axiom proof_of_atype_unify_partial_solve_wit_8 : atype_unify_partial_solve_wit_8.
Axiom proof_of_atype_unify_partial_solve_wit_9_pure : atype_unify_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify_partial_solve_wit_9 : atype_unify_partial_solve_wit_9.
Axiom proof_of_atype_unify_partial_solve_wit_10_pure : atype_unify_partial_solve_wit_10_pure.
Axiom proof_of_atype_unify_partial_solve_wit_10 : atype_unify_partial_solve_wit_10.
Axiom proof_of_atype_unify_partial_solve_wit_11_pure : atype_unify_partial_solve_wit_11_pure.
Axiom proof_of_atype_unify_partial_solve_wit_11 : atype_unify_partial_solve_wit_11.
Axiom proof_of_atype_unify_partial_solve_wit_12_pure : atype_unify_partial_solve_wit_12_pure.
Axiom proof_of_atype_unify_partial_solve_wit_12 : atype_unify_partial_solve_wit_12.
Axiom proof_of_atype_unify_which_implies_wit_1 : atype_unify_which_implies_wit_1.
Axiom proof_of_atype_unify_which_implies_wit_2 : atype_unify_which_implies_wit_2.
Axiom proof_of_atype_unify_which_implies_wit_3 : atype_unify_which_implies_wit_3.
Axiom proof_of_atype_unify_which_implies_wit_4 : atype_unify_which_implies_wit_4.
Axiom proof_of_atype_unify_which_implies_wit_5 : atype_unify_which_implies_wit_5.
Axiom proof_of_atype_unify1_safety_wit_1 : atype_unify1_safety_wit_1.
Axiom proof_of_atype_unify1_return_wit_1 : atype_unify1_return_wit_1.
Axiom proof_of_atype_unify1_return_wit_2 : atype_unify1_return_wit_2.
Axiom proof_of_atype_unify1_return_wit_3 : atype_unify1_return_wit_3.
Axiom proof_of_atype_unify1_return_wit_4 : atype_unify1_return_wit_4.
Axiom proof_of_atype_unify1_return_wit_5 : atype_unify1_return_wit_5.
Axiom proof_of_atype_unify1_return_wit_6 : atype_unify1_return_wit_6.
Axiom proof_of_atype_unify1_partial_solve_wit_1 : atype_unify1_partial_solve_wit_1.
Axiom proof_of_atype_unify1_partial_solve_wit_2_pure : atype_unify1_partial_solve_wit_2_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_2 : atype_unify1_partial_solve_wit_2.
Axiom proof_of_atype_unify1_partial_solve_wit_3_pure : atype_unify1_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_3 : atype_unify1_partial_solve_wit_3.
Axiom proof_of_atype_unify1_partial_solve_wit_4_pure : atype_unify1_partial_solve_wit_4_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_4 : atype_unify1_partial_solve_wit_4.
Axiom proof_of_atype_unify1_partial_solve_wit_5_pure : atype_unify1_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_5 : atype_unify1_partial_solve_wit_5.
Axiom proof_of_atype_unify1_partial_solve_wit_6_pure : atype_unify1_partial_solve_wit_6_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_6 : atype_unify1_partial_solve_wit_6.
Axiom proof_of_atype_unify1_partial_solve_wit_7 : atype_unify1_partial_solve_wit_7.
Axiom proof_of_atype_unify1_partial_solve_wit_8 : atype_unify1_partial_solve_wit_8.
Axiom proof_of_atype_unify1_partial_solve_wit_9_pure : atype_unify1_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_9 : atype_unify1_partial_solve_wit_9.
Axiom proof_of_atype_unify1_partial_solve_wit_10_pure : atype_unify1_partial_solve_wit_10_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_10 : atype_unify1_partial_solve_wit_10.
Axiom proof_of_atype_unify1_partial_solve_wit_11_pure : atype_unify1_partial_solve_wit_11_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_11 : atype_unify1_partial_solve_wit_11.
Axiom proof_of_atype_unify1_partial_solve_wit_12_pure : atype_unify1_partial_solve_wit_12_pure.
Axiom proof_of_atype_unify1_partial_solve_wit_12 : atype_unify1_partial_solve_wit_12.
Axiom proof_of_atype_unify1_which_implies_wit_1 : atype_unify1_which_implies_wit_1.
Axiom proof_of_atype_unify1_which_implies_wit_2 : atype_unify1_which_implies_wit_2.
Axiom proof_of_atype_unify1_which_implies_wit_3 : atype_unify1_which_implies_wit_3.
Axiom proof_of_atype_unify1_which_implies_wit_4 : atype_unify1_which_implies_wit_4.
Axiom proof_of_atype_unify1_which_implies_wit_5 : atype_unify1_which_implies_wit_5.
Axiom proof_of_atype_unify2_safety_wit_1 : atype_unify2_safety_wit_1.
Axiom proof_of_atype_unify2_safety_wit_2 : atype_unify2_safety_wit_2.
Axiom proof_of_atype_unify2_safety_wit_3 : atype_unify2_safety_wit_3.
Axiom proof_of_atype_unify2_safety_wit_4 : atype_unify2_safety_wit_4.
Axiom proof_of_atype_unify2_safety_wit_5 : atype_unify2_safety_wit_5.
Axiom proof_of_atype_unify2_safety_wit_6 : atype_unify2_safety_wit_6.
Axiom proof_of_atype_unify2_safety_wit_7 : atype_unify2_safety_wit_7.
Axiom proof_of_atype_unify2_safety_wit_8 : atype_unify2_safety_wit_8.
Axiom proof_of_atype_unify2_safety_wit_9 : atype_unify2_safety_wit_9.
Axiom proof_of_atype_unify2_safety_wit_10 : atype_unify2_safety_wit_10.
Axiom proof_of_atype_unify2_safety_wit_11 : atype_unify2_safety_wit_11.
Axiom proof_of_atype_unify2_safety_wit_12 : atype_unify2_safety_wit_12.
Axiom proof_of_atype_unify2_safety_wit_13 : atype_unify2_safety_wit_13.
Axiom proof_of_atype_unify2_safety_wit_14 : atype_unify2_safety_wit_14.
Axiom proof_of_atype_unify2_safety_wit_15 : atype_unify2_safety_wit_15.
Axiom proof_of_atype_unify2_safety_wit_16 : atype_unify2_safety_wit_16.
Axiom proof_of_atype_unify2_safety_wit_17 : atype_unify2_safety_wit_17.
Axiom proof_of_atype_unify2_safety_wit_18 : atype_unify2_safety_wit_18.
Axiom proof_of_atype_unify2_safety_wit_19 : atype_unify2_safety_wit_19.
Axiom proof_of_atype_unify2_safety_wit_20 : atype_unify2_safety_wit_20.
Axiom proof_of_atype_unify2_safety_wit_21 : atype_unify2_safety_wit_21.
Axiom proof_of_atype_unify2_safety_wit_22 : atype_unify2_safety_wit_22.
Axiom proof_of_atype_unify2_safety_wit_23 : atype_unify2_safety_wit_23.
Axiom proof_of_atype_unify2_entail_wit_1_1 : atype_unify2_entail_wit_1_1.
Axiom proof_of_atype_unify2_entail_wit_1_2 : atype_unify2_entail_wit_1_2.
Axiom proof_of_atype_unify2_entail_wit_2_1 : atype_unify2_entail_wit_2_1.
Axiom proof_of_atype_unify2_entail_wit_2_2 : atype_unify2_entail_wit_2_2.
Axiom proof_of_atype_unify2_entail_wit_3_1 : atype_unify2_entail_wit_3_1.
Axiom proof_of_atype_unify2_entail_wit_3_2 : atype_unify2_entail_wit_3_2.
Axiom proof_of_atype_unify2_entail_wit_4_1 : atype_unify2_entail_wit_4_1.
Axiom proof_of_atype_unify2_entail_wit_4_2 : atype_unify2_entail_wit_4_2.
Axiom proof_of_atype_unify2_return_wit_1 : atype_unify2_return_wit_1.
Axiom proof_of_atype_unify2_return_wit_2 : atype_unify2_return_wit_2.
Axiom proof_of_atype_unify2_return_wit_3 : atype_unify2_return_wit_3.
Axiom proof_of_atype_unify2_return_wit_4 : atype_unify2_return_wit_4.
Axiom proof_of_atype_unify2_return_wit_5 : atype_unify2_return_wit_5.
Axiom proof_of_atype_unify2_return_wit_6 : atype_unify2_return_wit_6.
Axiom proof_of_atype_unify2_return_wit_7 : atype_unify2_return_wit_7.
Axiom proof_of_atype_unify2_return_wit_8 : atype_unify2_return_wit_8.
Axiom proof_of_atype_unify2_return_wit_9 : atype_unify2_return_wit_9.
Axiom proof_of_atype_unify2_return_wit_10 : atype_unify2_return_wit_10.
Axiom proof_of_atype_unify2_return_wit_11 : atype_unify2_return_wit_11.
Axiom proof_of_atype_unify2_return_wit_12 : atype_unify2_return_wit_12.
Axiom proof_of_atype_unify2_return_wit_13 : atype_unify2_return_wit_13.
Axiom proof_of_atype_unify2_partial_solve_wit_1 : atype_unify2_partial_solve_wit_1.
Axiom proof_of_atype_unify2_partial_solve_wit_2_pure : atype_unify2_partial_solve_wit_2_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_2 : atype_unify2_partial_solve_wit_2.
Axiom proof_of_atype_unify2_partial_solve_wit_3_pure : atype_unify2_partial_solve_wit_3_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_3 : atype_unify2_partial_solve_wit_3.
Axiom proof_of_atype_unify2_partial_solve_wit_4 : atype_unify2_partial_solve_wit_4.
Axiom proof_of_atype_unify2_partial_solve_wit_5_pure : atype_unify2_partial_solve_wit_5_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_5 : atype_unify2_partial_solve_wit_5.
Axiom proof_of_atype_unify2_partial_solve_wit_6 : atype_unify2_partial_solve_wit_6.
Axiom proof_of_atype_unify2_partial_solve_wit_7_pure : atype_unify2_partial_solve_wit_7_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_7 : atype_unify2_partial_solve_wit_7.
Axiom proof_of_atype_unify2_partial_solve_wit_8 : atype_unify2_partial_solve_wit_8.
Axiom proof_of_atype_unify2_partial_solve_wit_9_pure : atype_unify2_partial_solve_wit_9_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_9 : atype_unify2_partial_solve_wit_9.
Axiom proof_of_atype_unify2_partial_solve_wit_10 : atype_unify2_partial_solve_wit_10.
Axiom proof_of_atype_unify2_partial_solve_wit_11_pure : atype_unify2_partial_solve_wit_11_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_11 : atype_unify2_partial_solve_wit_11.
Axiom proof_of_atype_unify2_partial_solve_wit_12_pure : atype_unify2_partial_solve_wit_12_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_12 : atype_unify2_partial_solve_wit_12.
Axiom proof_of_atype_unify2_partial_solve_wit_13 : atype_unify2_partial_solve_wit_13.
Axiom proof_of_atype_unify2_partial_solve_wit_14 : atype_unify2_partial_solve_wit_14.
Axiom proof_of_atype_unify2_partial_solve_wit_15_pure : atype_unify2_partial_solve_wit_15_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_15 : atype_unify2_partial_solve_wit_15.
Axiom proof_of_atype_unify2_partial_solve_wit_16 : atype_unify2_partial_solve_wit_16.
Axiom proof_of_atype_unify2_partial_solve_wit_17 : atype_unify2_partial_solve_wit_17.
Axiom proof_of_atype_unify2_partial_solve_wit_18_pure : atype_unify2_partial_solve_wit_18_pure.
Axiom proof_of_atype_unify2_partial_solve_wit_18 : atype_unify2_partial_solve_wit_18.
Axiom proof_of_atype_unify2_which_implies_wit_1 : atype_unify2_which_implies_wit_1.
Axiom proof_of_atype_unify2_which_implies_wit_2 : atype_unify2_which_implies_wit_2.
Axiom proof_of_atype_unify2_which_implies_wit_3 : atype_unify2_which_implies_wit_3.
Axiom proof_of_atype_unify2_which_implies_wit_4 : atype_unify2_which_implies_wit_4.
Axiom proof_of_atype_unify2_which_implies_wit_5 : atype_unify2_which_implies_wit_5.
Axiom proof_of_atype_unify2_which_implies_wit_6 : atype_unify2_which_implies_wit_6.
Axiom proof_of_atype_unify2_which_implies_wit_7 : atype_unify2_which_implies_wit_7.
Axiom proof_of_atype_unify2_which_implies_wit_8 : atype_unify2_which_implies_wit_8.
Axiom proof_of_atype_unify_derive_final_by_verify : atype_unify_derive_final_by_verify.

End VC_Correct.
