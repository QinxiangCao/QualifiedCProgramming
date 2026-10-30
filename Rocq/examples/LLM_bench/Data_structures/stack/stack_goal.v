From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.stack.stack_lib.
Local Open Scope sac.

(*----- Function push -----*)

Definition push_return_wit_1 :=
(
forall (before: sll) (stack_pre: Z) (n_pre: Z) (x_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < stack_capacity)),
  (((stack_pre + (n_pre * sizeof(INT)))) # Int  |-> x_pre)
  **  (store_stack stack_pre before n_pre )
|--
  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1 ) )
) \/
(
forall (before: sll) (stack_pre: Z) (n_pre: Z) (x_pre: Z) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < stack_capacity)),
  (((stack_pre + (n_pre * sizeof(INT)))) # Int  |-> x_pre)
  **  (store_stack stack_pre before n_pre )
|--
  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1 ) )
).

Definition push_return_wit_1_split_goal_spatial :=
forall (before: sll) (stack_pre: Z) (n_pre: Z) (x_pre: Z) (PreH1 : (x_pre <= INT_MAX)) (PreH2 : (x_pre >= INT_MIN)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < stack_capacity)),
  (((stack_pre + (n_pre * sizeof(INT)))) # Int  |-> x_pre)
  **  (store_stack stack_pre before n_pre )
|--
  (store_stack stack_pre (sll_cons (x_pre) (before)) (n_pre + 1 ) )
.

Definition push_partial_solve_wit_1 :=
forall (before: sll) (stack_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < stack_capacity)),
  (store_stack stack_pre before n_pre )
  **  (IntArray.undef_seg stack_pre n_pre (n_pre + 1 ) )
|--
  “ (0 <= n_pre) ”
  &&  “ (n_pre < stack_capacity) ”
  &&  (((stack_pre + (n_pre * sizeof(INT)))) # Int  |->_)
  **  (store_stack stack_pre before n_pre )
.

(*----- Function pop -----*)

Definition pop_safety_wit_1 :=
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (concrete: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (stack_representation (sll_cons (top) (rest)) concrete n_pre )),
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "stack" ) )) # Ptr  |-> stack_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full stack_pre n_pre concrete )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition pop_safety_wit_2 :=
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (concrete: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (stack_representation (sll_cons (top) (rest)) concrete n_pre )),
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "stack" ) )) # Ptr  |-> stack_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full stack_pre n_pre concrete )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition pop_entail_wit_1 :=
(
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)),
  (store_stack stack_pre (sll_cons (top) (rest)) n_pre )
|--
  EX (concrete: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (stack_representation (sll_cons (top) (rest)) concrete n_pre ) ”
  &&  (IntArray.full stack_pre n_pre concrete )
) \/
(
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)),
  (store_stack stack_pre (sll_cons (top) (rest)) n_pre )
|--
  EX (concrete: (@list Z)),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (stack_representation (sll_cons (top) (rest)) concrete n_pre ) ”
  &&  (IntArray.full stack_pre n_pre concrete )
).

Definition pop_return_wit_1 :=
(
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (concrete: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (stack_representation (sll_cons (top) (rest)) concrete n_pre )),
  (IntArray.full stack_pre n_pre concrete )
|--
  “ ((Znth (n_pre - 1 ) concrete 0) = top) ”
  &&  (store_stack stack_pre rest (n_pre - 1 ) )
  **  (IntArray.undef_seg stack_pre (n_pre - 1 ) n_pre )
) \/
(
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (concrete: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (stack_representation (sll_cons (top) (rest)) concrete n_pre )),
  (IntArray.full stack_pre n_pre concrete )
|--
  “ ((Znth (n_pre - 1 ) concrete 0) = top) ”
  &&  (store_stack stack_pre rest (n_pre - 1 ) )
  **  (IntArray.undef_seg stack_pre (n_pre - 1 ) n_pre )
).

Definition pop_return_wit_1_split_goal_1 :=
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (concrete: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (stack_representation (sll_cons (top) (rest)) concrete n_pre )),
  (IntArray.full stack_pre n_pre concrete )
|--
  “ ((Znth (n_pre - 1 ) concrete 0) = top) ”
.

Definition pop_return_wit_1_split_goal_spatial :=
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (concrete: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (stack_representation (sll_cons (top) (rest)) concrete n_pre )),
  (IntArray.full stack_pre n_pre concrete )
|--
  (store_stack stack_pre rest (n_pre - 1 ) )
  **  (IntArray.undef_seg stack_pre (n_pre - 1 ) n_pre )
.

Definition pop_partial_solve_wit_1 :=
forall (rest: sll) (top: Z) (stack_pre: Z) (n_pre: Z) (concrete: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (stack_representation (sll_cons (top) (rest)) concrete n_pre )),
  (IntArray.full stack_pre n_pre concrete )
|--
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (stack_representation (sll_cons (top) (rest)) concrete n_pre ) ”
  &&  (((stack_pre + ((n_pre - 1 ) * sizeof(INT)))) # Int  |-> (Znth (n_pre - 1 ) concrete 0))
  **  (IntArray.missing_i stack_pre (n_pre - 1 ) 0 n_pre concrete )
.

(*----- Function build -----*)

Definition build_safety_wit_1 :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stack" ) )) # Ptr  |-> stack_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full stack_pre n_pre input )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_2 :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)),
  ((( &( "stack" ) )) # Ptr  |-> stack_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full stack_pre n_pre input )
|--
  “ False ”
.

Definition build_safety_wit_3 :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix: sll) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix input i )),
  (store_stack stack_pre (sll_cons (x) (prefix)) (i + 1 ) )
  **  ((( &( "stack" ) )) # Ptr  |-> stack_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_entail_wit_1 :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)),
  (IntArray.full stack_pre n_pre input )
|--
  (“ (n_pre = 0) ”
  &&  “ (1 = 1) ”
  &&  (IntArray.full stack_pre n_pre input ))
  ||
  (EX (prefix: sll),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= n_pre) ”
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  “ (BuildStackPrefix prefix input 1 ) ”
  &&  (store_stack stack_pre prefix 1 )
  **  (IntArray.seg stack_pre 1 n_pre (sublist (1) (n_pre) (input)) ))
.

Definition build_entail_wit_2 :=
(
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix_2: sll) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix_2 input i )),
  (IntArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)) )
  **  (store_stack stack_pre prefix_2 i )
|--
  EX (prefix: sll),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (input)) 0) = (Znth i input 0)) ”
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  “ (BuildStackPrefix prefix input i ) ”
  &&  (store_stack stack_pre prefix i )
  **  (IntArray.undef_seg stack_pre i (i + 1 ) )
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
) \/
(
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix_2: sll) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix_2 input i )),
  (IntArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)) )
  **  (store_stack stack_pre prefix_2 i )
|--
  EX (prefix: sll),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ ((Znth (i - i ) (sublist (i) (n_pre) (input)) 0) = (Znth i input 0)) ”
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  “ (BuildStackPrefix prefix input i ) ”
  &&  (store_stack stack_pre prefix i )
  **  (IntArray.undef_seg stack_pre i (i + 1 ) )
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
).

Definition build_entail_wit_3 :=
(
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix_2: sll) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix_2 input i )),
  (store_stack stack_pre (sll_cons (x) (prefix_2)) (i + 1 ) )
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  EX (prefix: sll),
  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  “ (BuildStackPrefix prefix input (i + 1 ) ) ”
  &&  (store_stack stack_pre prefix (i + 1 ) )
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
) \/
(
forall (input: (@list Z)) (n_pre: Z) (prefix_2: sll) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix_2 input i )),
  TT && emp 
|--
  “ (BuildStackPrefix (sll_cons (x) (prefix_2)) input (i + 1 ) ) ”
  &&  emp
).

Definition build_entail_wit_3_split_goal_1 :=
forall (input: (@list Z)) (n_pre: Z) (prefix_2: sll) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix_2 input i )),
  (BuildStackPrefix (sll_cons (x) (prefix_2)) input (i + 1 ) )
.

Definition build_return_wit_1 :=
(
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)),
  (IntArray.full stack_pre n_pre input )
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre )
) \/
(
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)),
  (IntArray.full stack_pre n_pre input )
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre )
).

Definition build_return_wit_1_split_goal_spatial :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = 0)) (PreH3 : (i = 1)),
  (IntArray.full stack_pre n_pre input )
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre )
.

Definition build_return_wit_2 :=
(
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix: sll) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix input i )),
  (store_stack stack_pre prefix i )
  **  (IntArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre )
) \/
(
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix: sll) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix input i )),
  (store_stack stack_pre prefix i )
  **  (IntArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre )
).

Definition build_return_wit_2_split_goal_spatial :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix: sll) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix input i )),
  (store_stack stack_pre prefix i )
  **  (IntArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  (store_stack stack_pre (sll_from_array (input)) n_pre )
.

Definition build_partial_solve_wit_1 :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix: sll) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= stack_capacity)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix input i )),
  (store_stack stack_pre prefix i )
  **  (IntArray.seg stack_pre i n_pre (sublist (i) (n_pre) (input)) )
|--
  “ (i < n_pre) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= n_pre) ”
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  “ (BuildStackPrefix prefix input i ) ”
  &&  (((stack_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - i ) (sublist (i) (n_pre) (input)) 0))
  **  (IntArray.missing_i stack_pre i i n_pre (sublist (i) (n_pre) (input)) )
  **  (store_stack stack_pre prefix i )
.

Definition build_partial_solve_wit_2_pure :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix: sll) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix input i )),
  ((( &( "stack" ) )) # Ptr  |-> stack_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  (store_stack stack_pre prefix i )
  **  (IntArray.undef_seg stack_pre i (i + 1 ) )
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  “ (0 <= i) ”
  &&  “ (i < stack_capacity) ”
.

Definition build_partial_solve_wit_2_aux :=
forall (input: (@list Z)) (stack_pre: Z) (n_pre: Z) (prefix: sll) (i: Z) (x: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= stack_capacity)) (PreH3 : (1 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (x = (Znth i input 0))) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (BuildStackPrefix prefix input i )),
  (store_stack stack_pre prefix i )
  **  (IntArray.undef_seg stack_pre i (i + 1 ) )
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
|--
  “ (0 <= i) ”
  &&  “ (i < stack_capacity) ”
  &&  “ (1 <= n_pre) ”
  &&  “ (n_pre <= stack_capacity) ”
  &&  “ (1 <= i) ”
  &&  “ (i < n_pre) ”
  &&  “ (x = (Znth i input 0)) ”
  &&  “ ((Zlength (input)) = n_pre) ”
  &&  “ (BuildStackPrefix prefix input i ) ”
  &&  (store_stack stack_pre prefix i )
  **  (IntArray.undef_seg stack_pre i (i + 1 ) )
  **  (IntArray.seg stack_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (input)) )
.

Definition build_partial_solve_wit_2 := build_partial_solve_wit_2_pure -> build_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_push_return_wit_1 : push_return_wit_1.
Axiom proof_of_push_partial_solve_wit_1 : push_partial_solve_wit_1.
Axiom proof_of_pop_safety_wit_1 : pop_safety_wit_1.
Axiom proof_of_pop_safety_wit_2 : pop_safety_wit_2.
Axiom proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Axiom proof_of_pop_return_wit_1 : pop_return_wit_1.
Axiom proof_of_pop_partial_solve_wit_1 : pop_partial_solve_wit_1.
Axiom proof_of_build_safety_wit_1 : build_safety_wit_1.
Axiom proof_of_build_safety_wit_2 : build_safety_wit_2.
Axiom proof_of_build_safety_wit_3 : build_safety_wit_3.
Axiom proof_of_build_entail_wit_1 : build_entail_wit_1.
Axiom proof_of_build_entail_wit_2 : build_entail_wit_2.
Axiom proof_of_build_entail_wit_3 : build_entail_wit_3.
Axiom proof_of_build_return_wit_1 : build_return_wit_1.
Axiom proof_of_build_return_wit_2 : build_return_wit_2.
Axiom proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1.
Axiom proof_of_build_partial_solve_wit_2_pure : build_partial_solve_wit_2_pure.
Axiom proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2.

End VC_Correct.
