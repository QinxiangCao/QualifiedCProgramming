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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written 0) = 1))) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (written) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written 0) = 1))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  (IntArray.undef_full out_pre n_pre )
|--
  EX (written: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (written)) = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k written 0) = 1)) ”
  &&  (IntArray.seg out_pre 0 0 written )
  **  (IntArray.undef_seg out_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k (@nil Z) 0) = 1)) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k (@nil Z) 0) = 1))
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (written_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written_2 0) = 1))) ,
  (IntArray.seg out_pre 0 (i + 1 ) (app (written_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
|--
  EX (written: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (written)) = (i + 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k written 0) = 1)) ”
  &&  (IntArray.seg out_pre 0 (i + 1 ) written )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (written_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written_2 0) = 1))) ,
  TT && emp 
|--
  “ ((Zlength ((app (written_2) ((cons (1) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (written_2: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written_2)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written_2 0) = 1))) ,
  ((Zlength ((app (written_2) ((cons (1) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written 0) = 1))) ,
  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  EX (out_spec: (@list Z)) ,
  “ (Spec n_pre out_spec ) ”
  &&  (IntArray.full out_pre n_pre out_spec )
) \/
(
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written 0) = 1))) ,
  (IntArray.seg out_pre 0 i written )
|--
  EX (out_spec: (@list Z)) ,
  “ (Spec n_pre out_spec ) ”
  &&  (IntArray.full out_pre n_pre out_spec )
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (written: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (written)) = i)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written 0) = 1))) ,
  (IntArray.seg out_pre 0 i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (written)) = i) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k written 0) = 1)) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (IntArray.seg out_pre 0 i written )
.

Module Type VC_Correct.


Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
