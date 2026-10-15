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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P022_705B_spider_man_lib.
Local Open Scope sac.

(*----- Function next_parity -----*)

Definition next_parity_safety_wit_1 := 
forall (a_pre: Z) (par_pre: Z) (PreH1 : (0 <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int  |-> par_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
|--
  “ ((par_pre + (a_pre - 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (par_pre + (a_pre - 1 ) )) ”
.

Definition next_parity_safety_wit_2 := 
forall (a_pre: Z) (par_pre: Z) (PreH1 : (0 <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int  |-> par_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
|--
  “ ((a_pre - 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a_pre - 1 )) ”
.

Definition next_parity_safety_wit_3 := 
forall (a_pre: Z) (par_pre: Z) (PreH1 : (0 <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int  |-> par_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition next_parity_safety_wit_4 := 
forall (a_pre: Z) (par_pre: Z) (PreH1 : (0 <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  ((( &( "par" ) )) # Int  |-> par_pre)
  **  ((( &( "a" ) )) # Int64  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition next_parity_return_wit_1 := 
(
forall (a_pre: Z) (par_pre: Z) (PreH1 : (0 <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (NextParity par_pre a_pre (Z.land (par_pre + (a_pre - 1 ) ) 1) ) ”
  &&  emp
) \/
(
forall (a_pre: Z) (par_pre: Z) (PreH1 : (0 <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  TT && emp 
|--
  “ (NextParity par_pre a_pre (Z.land (par_pre + (a_pre - 1 ) ) 1) ) ”
  &&  emp
).

Definition next_parity_return_wit_1_split_goal_1 := 
forall (a_pre: Z) (par_pre: Z) (PreH1 : (0 <= par_pre)) (PreH2 : (par_pre <= 1)) (PreH3 : (1 <= a_pre)) (PreH4 : (a_pre <= 1000000000)) ,
  (NextParity par_pre a_pre (Z.land (par_pre + (a_pre - 1 ) ) 1) )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i added_values 0)) /\ ((Znth i added_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  ((( &( "par" ) )) # Int  |->_)
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full_shape out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i added_values 0)) /\ ((Znth i added_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "par" ) )) # Int  |-> 0)
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full_shape out_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> retval)
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> retval)
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (IntArray.full out_pre (i + 1 ) (app (written) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> retval)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (IntArray.full out_pre (i + 1 ) (app (written) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> retval)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i added_values 0)) /\ ((Znth i added_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full_shape out_pre n_pre )
|--
  EX (written: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (added_values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (SpiderPrefixState (sublist (0) (0) (added_values)) written 0 ) ”
  &&  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre 0 written )
  **  (IntArray.undef_seg out_pre 0 n_pre )
) \/
(
forall (out_pre: Z) (n_pre: Z) (added_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i added_values 0)) /\ ((Znth i added_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ (SpiderPrefixState (sublist (0) (0) (added_values)) (@nil Z) 0 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ”
  &&  (IntArray.undef_seg out_pre 0 n_pre )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (added_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i added_values 0)) /\ ((Znth i added_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ (SpiderPrefixState (sublist (0) (0) (added_values)) (@nil Z) 0 ) ”
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (out_pre: Z) (n_pre: Z) (added_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i added_values 0)) /\ ((Znth i added_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (out_pre: Z) (n_pre: Z) (added_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i added_values 0)) /\ ((Znth i added_values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (added_values)))) ,
  (IntArray.full_shape out_pre n_pre )
|--
  (IntArray.undef_seg out_pre 0 n_pre )
.

Definition solver_entail_wit_2_1 := 
(
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written_2: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written_2 par )) ,
  (IntArray.full out_pre (i + 1 ) (app (written_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full added_pre n_pre added_values )
|--
  EX (written: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (added_values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (SpiderPrefixState (sublist (0) ((i + 1 )) (added_values)) written retval ) ”
  &&  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre (i + 1 ) written )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (added_values: (@list Z)) (written_2: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written_2 par )) ,
  TT && emp 
|--
  “ (SpiderPrefixState (sublist (0) ((i + 1 )) (added_values)) (app (written_2) ((cons (1) ((@nil Z))))) retval ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (added_values: (@list Z)) (written_2: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written_2 par )) ,
  (SpiderPrefixState (sublist (0) ((i + 1 )) (added_values)) (app (written_2) ((cons (1) ((@nil Z))))) retval )
.

Definition solver_entail_wit_2_2 := 
(
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written_2: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written_2 par )) ,
  (IntArray.full out_pre (i + 1 ) (app (written_2) ((cons (2) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full added_pre n_pre added_values )
|--
  EX (written: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (added_values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (SpiderPrefixState (sublist (0) ((i + 1 )) (added_values)) written retval ) ”
  &&  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre (i + 1 ) written )
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (added_values: (@list Z)) (written_2: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written_2 par )) ,
  TT && emp 
|--
  “ (SpiderPrefixState (sublist (0) ((i + 1 )) (added_values)) (app (written_2) ((cons (2) ((@nil Z))))) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (added_values: (@list Z)) (written_2: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written_2 par )) ,
  (SpiderPrefixState (sublist (0) ((i + 1 )) (added_values)) (app (written_2) ((cons (2) ((@nil Z))))) 0 )
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  EX (result: (@list Z)) ,
  “ (Spec added_values result ) ”
  &&  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre n_pre result )
) \/
(
forall (out_pre: Z) (n_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (IntArray.full out_pre i written )
|--
  EX (result: (@list Z)) ,
  “ (Spec added_values result ) ”
  &&  (IntArray.full out_pre n_pre result )
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (added_values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SpiderPrefixState (sublist (0) (i) (added_values)) written par ) ”
  &&  (((added_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i added_values 0))
  **  (Int64Array.missing_i added_pre i 0 n_pre added_values )
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_2_pure := 
(
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> par)
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (1 <= (Znth i added_values 0)) ” 
  &&  “ ((Znth i added_values 0) <= 1000000000) ” 
  &&  “ (par <= 1) ” 
  &&  “ (0 <= par) ”
) \/
(
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (par <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (par >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (n_pre = (Zlength (added_values)))) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> par)
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (0 <= par) ” 
  &&  “ (par <= 1) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (par <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (par >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (n_pre = (Zlength (added_values)))) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> par)
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (0 <= par) ”
.

Definition solver_partial_solve_wit_2_pure_split_goal_2 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (par <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (par >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i < n_pre)) (PreH8 : (1 <= n_pre)) (PreH9 : (n_pre <= 100000)) (PreH10 : (n_pre = (Zlength (added_values)))) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  ((( &( "added" ) )) # Ptr  |-> added_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "par" ) )) # Int  |-> par)
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (par <= 1) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (added_values)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (1 <= (Znth i added_values 0)) ” 
  &&  “ ((Znth i added_values 0) <= 1000000000) ” 
  &&  “ (par <= 1) ” 
  &&  “ (0 <= par) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (added_values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SpiderPrefixState (sublist (0) (i) (added_values)) written par ) ”
  &&  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (retval <> 0) ” 
  &&  “ (NextParity par (Znth i added_values 0) retval ) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (added_values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SpiderPrefixState (sublist (0) (i) (added_values)) written par ) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (added_pre: Z) (added_values: (@list Z)) (written: (@list Z)) (par: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (NextParity par (Znth i added_values 0) retval )) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (added_values)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (SpiderPrefixState (sublist (0) (i) (added_values)) written par )) ,
  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
  **  (IntArray.undef_seg out_pre i n_pre )
|--
  “ (retval = 0) ” 
  &&  “ (NextParity par (Znth i added_values 0) retval ) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (added_values))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((1 <= (Znth j added_values 0)) /\ ((Znth j added_values 0) <= 1000000000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (SpiderPrefixState (sublist (0) (i) (added_values)) written par ) ”
  &&  (((out_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) n_pre )
  **  (Int64Array.full added_pre n_pre added_values )
  **  (IntArray.full out_pre i written )
.

Module Type VC_Correct.


Axiom proof_of_next_parity_safety_wit_1 : next_parity_safety_wit_1.
Axiom proof_of_next_parity_safety_wit_2 : next_parity_safety_wit_2.
Axiom proof_of_next_parity_safety_wit_3 : next_parity_safety_wit_3.
Axiom proof_of_next_parity_safety_wit_4 : next_parity_safety_wit_4.
Axiom proof_of_next_parity_return_wit_1 : next_parity_return_wit_1.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
