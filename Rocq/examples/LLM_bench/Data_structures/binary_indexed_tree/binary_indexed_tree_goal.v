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
Require Import SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib.
Local Open Scope sac.

(*----- Function lowbit -----*)

Definition lowbit_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition lowbit_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre))) ” 
  &&  “ (1 <= (Z.land x_pre (-x_pre))) ” 
  &&  “ ((Z.land x_pre (-x_pre)) <= x_pre) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.land x_pre (-x_pre)) <= x_pre) ” 
  &&  “ (1 <= (Z.land x_pre (-x_pre))) ” 
  &&  “ ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre))) ”
  &&  emp
).

Definition lowbit_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((Z.land x_pre (-x_pre)) <= x_pre)
.

Definition lowbit_return_wit_1_split_goal_2 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  (1 <= (Z.land x_pre (-x_pre)))
.

Definition lowbit_return_wit_1_split_goal_3 := 
forall (x_pre: Z) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre)))
.

(*----- Function add -----*)

Definition add_safety_wit_1 := 
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "delta" ) )) # Int  |-> delta_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (((Znth pos bit_cur 0) + delta_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos bit_cur 0) + delta_pre )) ”
) \/
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "delta" ) )) # Int  |-> delta_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (((Znth pos bit_cur 0) + delta_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos bit_cur 0) + delta_pre )) ”
).

Definition add_safety_wit_1_split_goal_1 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "delta" ) )) # Int  |-> delta_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (((Znth pos bit_cur 0) + delta_pre ) <= INT_MAX) ”
.

Definition add_safety_wit_1_split_goal_2 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "delta" ) )) # Int  |-> delta_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ ((INT_MIN) <= ((Znth pos bit_cur 0) + delta_pre )) ”
.

Definition add_safety_wit_2 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre ) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre ))) (PreH11 : (FenwickRep a bit_l n_pre )) (PreH12 : (FenwickIntervalsIntSafe a n_pre )) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH14 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) (replace_Znth (pos) (((Znth pos bit_cur 0) + delta_pre )) (bit_cur)) )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "delta" ) )) # Int  |-> delta_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ ((pos + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + retval )) ”
.

Definition add_entail_wit_1 := 
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre ) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre )) (PreH6 : (FenwickIntervalsIntSafe a n_pre )) (PreH7 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_l )
|--
  EX (bit_cur: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ (1 <= pos_pre) ” 
  &&  “ (pos_pre <= n_pre) ” 
  &&  “ (1 <= pos_pre) ” 
  &&  “ (pos_pre <= (2 * n_pre )) ” 
  &&  “ (FenwickRep a bit_l n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe a n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre ) ” 
  &&  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos_pre delta_pre ) ”
  &&  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
) \/
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre ) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre )) (PreH6 : (FenwickIntervalsIntSafe a n_pre )) (PreH7 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) ,
  TT && emp 
|--
  “ (FenwickAddProgress bit_l bit_l n_pre pos_pre pos_pre delta_pre ) ”
  &&  emp
).

Definition add_entail_wit_1_split_goal_1 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre ) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre )) (PreH6 : (FenwickIntervalsIntSafe a n_pre )) (PreH7 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) ,
  (FenwickAddProgress bit_l bit_l n_pre pos_pre pos_pre delta_pre )
.

Definition add_entail_wit_2 := 
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur_2: (@list Z)) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre ) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre ))) (PreH11 : (FenwickRep a bit_l n_pre )) (PreH12 : (FenwickIntervalsIntSafe a n_pre )) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH14 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) (replace_Znth (pos) (((Znth pos bit_cur_2 0) + delta_pre )) (bit_cur_2)) )
|--
  EX (bit_cur: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ (1 <= pos_pre) ” 
  &&  “ (pos_pre <= n_pre) ” 
  &&  “ (1 <= (pos + retval )) ” 
  &&  “ ((pos + retval ) <= (2 * n_pre )) ” 
  &&  “ (FenwickRep a bit_l n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe a n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre ) ” 
  &&  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre (pos + retval ) delta_pre ) ”
  &&  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
) \/
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur_2: (@list Z)) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre ) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre ))) (PreH11 : (FenwickRep a bit_l n_pre )) (PreH12 : (FenwickIntervalsIntSafe a n_pre )) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH14 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre )) ,
  TT && emp 
|--
  “ (FenwickAddProgress bit_l (replace_Znth (pos) (((Znth pos bit_cur_2 0) + delta_pre )) (bit_cur_2)) n_pre pos_pre (pos + retval ) delta_pre ) ”
  &&  emp
).

Definition add_entail_wit_2_split_goal_1 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur_2: (@list Z)) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos <= n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : ((2 * n_pre ) <= INT_MAX)) (PreH7 : (1 <= pos_pre)) (PreH8 : (pos_pre <= n_pre)) (PreH9 : (1 <= pos)) (PreH10 : (pos <= (2 * n_pre ))) (PreH11 : (FenwickRep a bit_l n_pre )) (PreH12 : (FenwickIntervalsIntSafe a n_pre )) (PreH13 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH14 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre )) ,
  (FenwickAddProgress bit_l (replace_Znth (pos) (((Znth pos bit_cur_2 0) + delta_pre )) (bit_cur_2)) n_pre pos_pre (pos + retval ) delta_pre )
.

Definition add_return_wit_1 := 
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
|--
  EX (bit_l1: (@list Z)) ,
  “ (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_l1 n_pre ) ” 
  &&  “ ((Znth (0) (bit_l1) (0)) = (Znth (0) (bit_l) (0))) ”
  &&  (IntArray.full bit_pre (n_pre + 1 ) bit_l1 )
) \/
(
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  TT && emp 
|--
  “ ((Znth (0) (bit_cur) (0)) = (Znth (0) (bit_l) (0))) ” 
  &&  “ (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_cur n_pre ) ”
  &&  emp
).

Definition add_return_wit_1_split_goal_1 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  ((Znth (0) (bit_cur) (0)) = (Znth (0) (bit_l) (0)))
.

Definition add_return_wit_1_split_goal_2 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_cur n_pre )
.

Definition add_partial_solve_wit_1 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
|--
  “ (pos <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ (1 <= pos_pre) ” 
  &&  “ (pos_pre <= n_pre) ” 
  &&  “ (1 <= pos) ” 
  &&  “ (pos <= (2 * n_pre )) ” 
  &&  “ (FenwickRep a bit_l n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe a n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre ) ” 
  &&  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre ) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int  |-> (Znth pos bit_cur 0))
  **  (IntArray.missing_i bit_pre pos 0 (n_pre + 1 ) bit_cur )
.

Definition add_partial_solve_wit_2 := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) bit_cur )
|--
  “ (pos <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ (1 <= pos_pre) ” 
  &&  “ (pos_pre <= n_pre) ” 
  &&  “ (1 <= pos) ” 
  &&  “ (pos <= (2 * n_pre )) ” 
  &&  “ (FenwickRep a bit_l n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe a n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre ) ” 
  &&  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre ) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i bit_pre pos 0 (n_pre + 1 ) bit_cur )
.

Definition add_partial_solve_wit_3_pure := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) (replace_Znth (pos) (((Znth pos bit_cur 0) + delta_pre )) (bit_cur)) )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "delta" ) )) # Int  |-> delta_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
|--
  “ (1 <= pos) ” 
  &&  “ (pos <= INT_MAX) ”
.

Definition add_partial_solve_wit_3_aux := 
forall (delta_pre: Z) (pos_pre: Z) (n_pre: Z) (bit_pre: Z) (bit_l: (@list Z)) (a: (@list Z)) (bit_cur: (@list Z)) (pos: Z) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre ) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre ))) (PreH8 : (FenwickRep a bit_l n_pre )) (PreH9 : (FenwickIntervalsIntSafe a n_pre )) (PreH10 : (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre )) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre )) ,
  (IntArray.full bit_pre (n_pre + 1 ) (replace_Znth (pos) (((Znth pos bit_cur 0) + delta_pre )) (bit_cur)) )
|--
  “ (1 <= pos) ” 
  &&  “ (pos <= INT_MAX) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ (1 <= pos_pre) ” 
  &&  “ (pos_pre <= n_pre) ” 
  &&  “ (1 <= pos) ” 
  &&  “ (pos <= (2 * n_pre )) ” 
  &&  “ (FenwickRep a bit_l n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe a n_pre ) ” 
  &&  “ (FenwickIntervalsIntSafe (FenwickAddArray (a) (pos_pre) (delta_pre)) n_pre ) ” 
  &&  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre ) ”
  &&  (IntArray.full bit_pre (n_pre + 1 ) (replace_Znth (pos) (((Znth pos bit_cur 0) + delta_pre )) (bit_cur)) )
.

Definition add_partial_solve_wit_3 := add_partial_solve_wit_3_pure -> add_partial_solve_wit_3_aux.

(*----- Function query -----*)

Definition query_safety_wit_1 := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (0 <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n )) (PreH6 : (FenwickIntervalsIntSafe a n )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  (IntArray.full bit_pre (n + 1 ) bit_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition query_safety_wit_2 := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (0 <= pos)) (PreH4 : (pos <= pos_pre)) (PreH5 : (pos_pre <= n)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (FenwickRep a bit_l n )) (PreH9 : (FenwickIntervalsIntSafe a n )) (PreH10 : (FenwickQueryState a pos_pre pos sum )) ,
  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full bit_pre (n + 1 ) bit_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition query_safety_wit_3 := 
(
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos > 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth pos bit_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth pos bit_l 0) )) ”
) \/
(
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos > 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth pos bit_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth pos bit_l 0) )) ”
).

Definition query_safety_wit_3_split_goal_1 := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos > 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth pos bit_l 0) ) <= INT_MAX) ”
.

Definition query_safety_wit_3_split_goal_2 := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos > 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + (Znth pos bit_l 0) )) ”
.

Definition query_safety_wit_4 := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > 0)) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n )) (PreH13 : (FenwickIntervalsIntSafe a n )) (PreH14 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth pos bit_l 0) ))
|--
  “ ((pos - retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos - retval )) ”
.

Definition query_entail_wit_1 := 
(
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (0 <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n )) (PreH6 : (FenwickIntervalsIntSafe a n )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
|--
  “ (1 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ (pos_pre <= pos_pre) ” 
  &&  “ (pos_pre <= n) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (FenwickRep a bit_l n ) ” 
  &&  “ (FenwickIntervalsIntSafe a n ) ” 
  &&  “ (FenwickQueryState a pos_pre pos_pre 0 ) ”
  &&  (IntArray.full bit_pre (n + 1 ) bit_l )
) \/
(
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (0 <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n )) (PreH6 : (FenwickIntervalsIntSafe a n )) ,
  TT && emp 
|--
  “ (FenwickQueryState a pos_pre pos_pre 0 ) ”
  &&  emp
).

Definition query_entail_wit_1_split_goal_1 := 
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : (0 <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n )) (PreH6 : (FenwickIntervalsIntSafe a n )) ,
  (FenwickQueryState a pos_pre pos_pre 0 )
.

Definition query_entail_wit_2 := 
(
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > 0)) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n )) (PreH13 : (FenwickIntervalsIntSafe a n )) (PreH14 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
|--
  “ (1 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= (pos - retval )) ” 
  &&  “ ((pos - retval ) <= pos_pre) ” 
  &&  “ (pos_pre <= n) ” 
  &&  “ (INT_MIN <= (sum + (Znth pos bit_l 0) )) ” 
  &&  “ ((sum + (Znth pos bit_l 0) ) <= INT_MAX) ” 
  &&  “ (FenwickRep a bit_l n ) ” 
  &&  “ (FenwickIntervalsIntSafe a n ) ” 
  &&  “ (FenwickQueryState a pos_pre (pos - retval ) (sum + (Znth pos bit_l 0) ) ) ”
  &&  (IntArray.full bit_pre (n + 1 ) bit_l )
) \/
(
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > 0)) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n )) (PreH13 : (FenwickIntervalsIntSafe a n )) (PreH14 : (FenwickQueryState a pos_pre pos sum )) ,
  TT && emp 
|--
  “ (FenwickQueryState a pos_pre (pos - retval ) (sum + (Znth pos bit_l 0) ) ) ” 
  &&  “ ((sum + (Znth pos bit_l 0) ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (sum + (Znth pos bit_l 0) )) ”
  &&  emp
).

Definition query_entail_wit_2_split_goal_1 := 
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > 0)) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n )) (PreH13 : (FenwickIntervalsIntSafe a n )) (PreH14 : (FenwickQueryState a pos_pre pos sum )) ,
  (FenwickQueryState a pos_pre (pos - retval ) (sum + (Znth pos bit_l 0) ) )
.

Definition query_entail_wit_2_split_goal_2 := 
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > 0)) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n )) (PreH13 : (FenwickIntervalsIntSafe a n )) (PreH14 : (FenwickQueryState a pos_pre pos sum )) ,
  ((sum + (Znth pos bit_l 0) ) <= INT_MAX)
.

Definition query_entail_wit_2_split_goal_3 := 
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (retval: Z) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (1 <= retval)) (PreH3 : (retval <= pos)) (PreH4 : (pos > 0)) (PreH5 : (1 <= n)) (PreH6 : (n <= INT_MAX)) (PreH7 : (0 <= pos)) (PreH8 : (pos <= pos_pre)) (PreH9 : (pos_pre <= n)) (PreH10 : (INT_MIN <= sum)) (PreH11 : (sum <= INT_MAX)) (PreH12 : (FenwickRep a bit_l n )) (PreH13 : (FenwickIntervalsIntSafe a n )) (PreH14 : (FenwickQueryState a pos_pre pos sum )) ,
  (INT_MIN <= (sum + (Znth pos bit_l 0) ))
.

Definition query_return_wit_1 := 
(
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos <= 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
|--
  “ (sum = (FenwickPrefixSum (a) (pos_pre))) ”
  &&  (IntArray.full bit_pre (n + 1 ) bit_l )
) \/
(
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos <= 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  TT && emp 
|--
  “ (sum = (FenwickPrefixSum (a) (pos_pre))) ”
  &&  emp
).

Definition query_return_wit_1_split_goal_1 := 
forall (pos_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos <= 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (sum = (FenwickPrefixSum (a) (pos_pre)))
.

Definition query_partial_solve_wit_1 := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos > 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
|--
  “ (pos > 0) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= pos_pre) ” 
  &&  “ (pos_pre <= n) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (FenwickRep a bit_l n ) ” 
  &&  “ (FenwickIntervalsIntSafe a n ) ” 
  &&  “ (FenwickQueryState a pos_pre pos sum ) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int  |-> (Znth pos bit_l 0))
  **  (IntArray.missing_i bit_pre pos 0 (n + 1 ) bit_l )
.

Definition query_partial_solve_wit_2_pure := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos > 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
  **  ((( &( "bit" ) )) # Ptr  |-> bit_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth pos bit_l 0) ))
|--
  “ (1 <= pos) ” 
  &&  “ (pos <= INT_MAX) ”
.

Definition query_partial_solve_wit_2_aux := 
forall (pos_pre: Z) (bit_pre: Z) (n: Z) (bit_l: (@list Z)) (a: (@list Z)) (sum: Z) (pos: Z) (PreH1 : (pos > 0)) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : (0 <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n )) (PreH10 : (FenwickIntervalsIntSafe a n )) (PreH11 : (FenwickQueryState a pos_pre pos sum )) ,
  (IntArray.full bit_pre (n + 1 ) bit_l )
|--
  “ (1 <= pos) ” 
  &&  “ (pos <= INT_MAX) ” 
  &&  “ (pos > 0) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= pos_pre) ” 
  &&  “ (pos_pre <= n) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ (FenwickRep a bit_l n ) ” 
  &&  “ (FenwickIntervalsIntSafe a n ) ” 
  &&  “ (FenwickQueryState a pos_pre pos sum ) ”
  &&  (IntArray.full bit_pre (n + 1 ) bit_l )
.

Definition query_partial_solve_wit_2 := query_partial_solve_wit_2_pure -> query_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_lowbit_safety_wit_1 : lowbit_safety_wit_1.
Axiom proof_of_lowbit_return_wit_1 : lowbit_return_wit_1.
Axiom proof_of_add_safety_wit_1 : add_safety_wit_1.
Axiom proof_of_add_safety_wit_2 : add_safety_wit_2.
Axiom proof_of_add_entail_wit_1 : add_entail_wit_1.
Axiom proof_of_add_entail_wit_2 : add_entail_wit_2.
Axiom proof_of_add_return_wit_1 : add_return_wit_1.
Axiom proof_of_add_partial_solve_wit_1 : add_partial_solve_wit_1.
Axiom proof_of_add_partial_solve_wit_2 : add_partial_solve_wit_2.
Axiom proof_of_add_partial_solve_wit_3_pure : add_partial_solve_wit_3_pure.
Axiom proof_of_add_partial_solve_wit_3 : add_partial_solve_wit_3.
Axiom proof_of_query_safety_wit_1 : query_safety_wit_1.
Axiom proof_of_query_safety_wit_2 : query_safety_wit_2.
Axiom proof_of_query_safety_wit_3 : query_safety_wit_3.
Axiom proof_of_query_safety_wit_4 : query_safety_wit_4.
Axiom proof_of_query_entail_wit_1 : query_entail_wit_1.
Axiom proof_of_query_entail_wit_2 : query_entail_wit_2.
Axiom proof_of_query_return_wit_1 : query_return_wit_1.
Axiom proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1.
Axiom proof_of_query_partial_solve_wit_2_pure : query_partial_solve_wit_2_pure.
Axiom proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2.

End VC_Correct.
