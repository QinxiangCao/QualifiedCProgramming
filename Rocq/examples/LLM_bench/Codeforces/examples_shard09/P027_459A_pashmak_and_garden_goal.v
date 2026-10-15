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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib.
Local Open Scope sac.

(*----- Function iabs -----*)

Definition iabs_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition iabs_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : ((-200) <= x_pre)) (PreH2 : (x_pre <= 200)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition iabs_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
).

Definition iabs_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  ((-x_pre) = (Z.abs (x_pre)))
.

Definition iabs_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
).

Definition iabs_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-200) <= x_pre)) (PreH3 : (x_pre <= 200)) ,
  (x_pre = (Z.abs (x_pre)))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre = x2_pre)) (PreH2 : ((-100) <= x1_pre)) (PreH3 : (x1_pre <= 100)) (PreH4 : ((-100) <= y1_pre)) (PreH5 : (y1_pre <= 100)) (PreH6 : ((-100) <= x2_pre)) (PreH7 : (x2_pre <= 100)) (PreH8 : ((-100) <= y2_pre)) (PreH9 : (y2_pre <= 100)) (PreH10 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((y1_pre - y2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y1_pre - y2_pre )) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((x1_pre + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x1_pre + retval )) ”
) \/
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((x1_pre + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x1_pre + retval )) ”
).

Definition solver_safety_wit_3_split_goal_1 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((x1_pre + retval ) <= INT_MAX) ”
.

Definition solver_safety_wit_3_split_goal_2 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((INT_MIN) <= (x1_pre + retval )) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
  **  (IntArray.undef_seg out_pre 1 4 )
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ ((x2_pre + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x2_pre + retval )) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> (x2_pre + retval ))
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((out_pre + (3 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> (x2_pre + retval ))
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre = y2_pre)) (PreH2 : (x1_pre <> x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((x1_pre - x2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x1_pre - x2_pre )) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 := 
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ ((y1_pre + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y1_pre + retval )) ”
) \/
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ ((y1_pre + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y1_pre + retval )) ”
).

Definition solver_safety_wit_12_split_goal_1 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ ((y1_pre + retval ) <= INT_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ ((INT_MIN) <= (y1_pre + retval )) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ ((y2_pre + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y2_pre + retval )) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((out_pre + (3 * sizeof(INT)))) # Int  |-> (y2_pre + retval ))
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  ((( &( "d" ) )) # Int  |-> retval)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre <> y2_pre)) (PreH2 : (x1_pre <> x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((x1_pre - x2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x1_pre - x2_pre )) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre <> y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((y1_pre - y2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y1_pre - y2_pre )) ”
.

Definition solver_safety_wit_19 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_22 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_23 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((out_pre + (3 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <> retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <> retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ (0 = 0) ” 
  &&  “ (NoCompletion x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (IntArray.undef_full out_pre 4 )
) \/
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <> retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  TT && emp 
|--
  “ (NoCompletion x1_pre y1_pre x2_pre y2_pre ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval <> retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (NoCompletion x1_pre y1_pre x2_pre y2_pre )
.

Definition solver_return_wit_2 := 
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((out_pre + (3 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  EX (x3: Z)  (y3: Z)  (x4: Z)  (y4: Z) ,
  “ (1 = 1) ” 
  &&  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4 ) ”
  &&  (IntArray.full out_pre 4 (cons (x3) ((cons (y3) ((cons (x4) ((cons (y4) ((@nil Z))))))))) )
) \/
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (x1_pre <= INT_MAX)) (PreH2 : (y2_pre <= INT_MAX)) (PreH3 : (x2_pre <= INT_MAX)) (PreH4 : (y1_pre <= INT_MAX)) (PreH5 : (x1_pre >= INT_MIN)) (PreH6 : (y2_pre >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : (y1_pre >= INT_MIN)) (PreH9 : (retval = retval_2)) (PreH10 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH11 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH12 : (y1_pre <> y2_pre)) (PreH13 : (x1_pre <> x2_pre)) (PreH14 : ((-100) <= x1_pre)) (PreH15 : (x1_pre <= 100)) (PreH16 : ((-100) <= y1_pre)) (PreH17 : (y1_pre <= 100)) (PreH18 : ((-100) <= x2_pre)) (PreH19 : (x2_pre <= 100)) (PreH20 : ((-100) <= y2_pre)) (PreH21 : (y2_pre <= 100)) (PreH22 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (3 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  EX (x3: Z)  (y3: Z)  (x4: Z)  (y4: Z) ,
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4 ) ”
  &&  (IntArray.full out_pre 4 (cons (x3) ((cons (y3) ((cons (x4) ((cons (y4) ((@nil Z))))))))) )
).

Definition solver_return_wit_3 := 
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((out_pre + (3 * sizeof(INT)))) # Int  |-> (y2_pre + retval ))
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  EX (x3: Z)  (y3: Z)  (x4: Z)  (y4: Z) ,
  “ (1 = 1) ” 
  &&  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4 ) ”
  &&  (IntArray.full out_pre 4 (cons (x3) ((cons (y3) ((cons (x4) ((cons (y4) ((@nil Z))))))))) )
) \/
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (x1_pre <= INT_MAX)) (PreH2 : ((y1_pre + retval ) <= INT_MAX)) (PreH3 : (x2_pre <= INT_MAX)) (PreH4 : ((y2_pre + retval ) <= INT_MAX)) (PreH5 : (x1_pre >= INT_MIN)) (PreH6 : ((y1_pre + retval ) >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : ((y2_pre + retval ) >= INT_MIN)) (PreH9 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH10 : (y1_pre = y2_pre)) (PreH11 : (x1_pre <> x2_pre)) (PreH12 : ((-100) <= x1_pre)) (PreH13 : (x1_pre <= 100)) (PreH14 : ((-100) <= y1_pre)) (PreH15 : (y1_pre <= 100)) (PreH16 : ((-100) <= x2_pre)) (PreH17 : (x2_pre <= 100)) (PreH18 : ((-100) <= y2_pre)) (PreH19 : (y2_pre <= 100)) (PreH20 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (3 * sizeof(INT)))) # Int  |-> (y2_pre + retval ))
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  EX (x3: Z)  (y3: Z)  (x4: Z)  (y4: Z) ,
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4 ) ”
  &&  (IntArray.full out_pre 4 (cons (x3) ((cons (y3) ((cons (x4) ((cons (y4) ((@nil Z))))))))) )
).

Definition solver_return_wit_4 := 
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((out_pre + (3 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> (x2_pre + retval ))
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
|--
  EX (x3: Z)  (y3: Z)  (x4: Z)  (y4: Z) ,
  “ (1 = 1) ” 
  &&  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4 ) ”
  &&  (IntArray.full out_pre 4 (cons (x3) ((cons (y3) ((cons (x4) ((cons (y4) ((@nil Z))))))))) )
) \/
(
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : ((x1_pre + retval ) <= INT_MAX)) (PreH2 : (y1_pre <= INT_MAX)) (PreH3 : ((x2_pre + retval ) <= INT_MAX)) (PreH4 : (y2_pre <= INT_MAX)) (PreH5 : ((x1_pre + retval ) >= INT_MIN)) (PreH6 : (y1_pre >= INT_MIN)) (PreH7 : ((x2_pre + retval ) >= INT_MIN)) (PreH8 : (y2_pre >= INT_MIN)) (PreH9 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH10 : (x1_pre = x2_pre)) (PreH11 : ((-100) <= x1_pre)) (PreH12 : (x1_pre <= 100)) (PreH13 : ((-100) <= y1_pre)) (PreH14 : (y1_pre <= 100)) (PreH15 : ((-100) <= x2_pre)) (PreH16 : (x2_pre <= 100)) (PreH17 : ((-100) <= y2_pre)) (PreH18 : (y2_pre <= 100)) (PreH19 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (3 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> (x2_pre + retval ))
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
|--
  EX (x3: Z)  (y3: Z)  (x4: Z)  (y4: Z) ,
  “ (CompletesSquare x1_pre y1_pre x2_pre y2_pre x3 y3 x4 y4 ) ”
  &&  (IntArray.full out_pre 4 (cons (x3) ((cons (y3) ((cons (x4) ((cons (y4) ((@nil Z))))))))) )
).

Definition solver_partial_solve_wit_1_pure := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre = x2_pre)) (PreH2 : ((-100) <= x1_pre)) (PreH3 : (x1_pre <= 100)) (PreH4 : ((-100) <= y1_pre)) (PreH5 : (y1_pre <= 100)) (PreH6 : ((-100) <= x2_pre)) (PreH7 : (x2_pre <= 100)) (PreH8 : ((-100) <= y2_pre)) (PreH9 : (y2_pre <= 100)) (PreH10 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (y1_pre - y2_pre )) ” 
  &&  “ ((y1_pre - y2_pre ) <= 200) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre = x2_pre)) (PreH2 : ((-100) <= x1_pre)) (PreH3 : (x1_pre <= 100)) (PreH4 : ((-100) <= y1_pre)) (PreH5 : (y1_pre <= 100)) (PreH6 : ((-100) <= x2_pre)) (PreH7 : (x2_pre <= 100)) (PreH8 : ((-100) <= y2_pre)) (PreH9 : (y2_pre <= 100)) (PreH10 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (y1_pre - y2_pre )) ” 
  &&  “ ((y1_pre - y2_pre ) <= 200) ” 
  &&  “ (x1_pre = x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (IntArray.undef_full out_pre 4 )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (x1_pre = x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre 1 4 )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
  **  (IntArray.undef_seg out_pre 1 4 )
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (x1_pre = x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (1 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (x1_pre = x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (2 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre 2 (1 + 1 ) 4 )
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((y1_pre - y2_pre ))))) (PreH2 : (x1_pre = x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> (x2_pre + retval ))
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
|--
  “ (retval = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (x1_pre = x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (3 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre 3 ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> (x2_pre + retval ))
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y1_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> (x1_pre + retval ))
.

Definition solver_partial_solve_wit_6_pure := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre = y2_pre)) (PreH2 : (x1_pre <> x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (x1_pre - x2_pre )) ” 
  &&  “ ((x1_pre - x2_pre ) <= 200) ”
.

Definition solver_partial_solve_wit_6_aux := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre = y2_pre)) (PreH2 : (x1_pre <> x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (x1_pre - x2_pre )) ” 
  &&  “ ((x1_pre - x2_pre ) <= 200) ” 
  &&  “ (y1_pre = y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (IntArray.undef_full out_pre 4 )
.

Definition solver_partial_solve_wit_6 := solver_partial_solve_wit_6_pure -> solver_partial_solve_wit_6_aux.

Definition solver_partial_solve_wit_7 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre = y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre 1 4 )
.

Definition solver_partial_solve_wit_8 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre = y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (1 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
.

Definition solver_partial_solve_wit_9 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre = y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (2 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre 2 (1 + 1 ) 4 )
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
.

Definition solver_partial_solve_wit_10 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre = y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre = y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (3 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre 3 ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> (y1_pre + retval ))
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
.

Definition solver_partial_solve_wit_11_pure := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre <> y2_pre)) (PreH2 : (x1_pre <> x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (x1_pre - x2_pre )) ” 
  &&  “ ((x1_pre - x2_pre ) <= 200) ”
.

Definition solver_partial_solve_wit_11_aux := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre <> y2_pre)) (PreH2 : (x1_pre <> x2_pre)) (PreH3 : ((-100) <= x1_pre)) (PreH4 : (x1_pre <= 100)) (PreH5 : ((-100) <= y1_pre)) (PreH6 : (y1_pre <= 100)) (PreH7 : ((-100) <= x2_pre)) (PreH8 : (x2_pre <= 100)) (PreH9 : ((-100) <= y2_pre)) (PreH10 : (y2_pre <= 100)) (PreH11 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (x1_pre - x2_pre )) ” 
  &&  “ ((x1_pre - x2_pre ) <= 200) ” 
  &&  “ (y1_pre <> y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (IntArray.undef_full out_pre 4 )
.

Definition solver_partial_solve_wit_11 := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux.

Definition solver_partial_solve_wit_12_pure := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre <> y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (y1_pre - y2_pre )) ” 
  &&  “ ((y1_pre - y2_pre ) <= 200) ”
.

Definition solver_partial_solve_wit_12_aux := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (PreH1 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH2 : (y1_pre <> y2_pre)) (PreH3 : (x1_pre <> x2_pre)) (PreH4 : ((-100) <= x1_pre)) (PreH5 : (x1_pre <= 100)) (PreH6 : ((-100) <= y1_pre)) (PreH7 : (y1_pre <= 100)) (PreH8 : ((-100) <= x2_pre)) (PreH9 : (x2_pre <= 100)) (PreH10 : ((-100) <= y2_pre)) (PreH11 : (y2_pre <= 100)) (PreH12 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ ((-200) <= (y1_pre - y2_pre )) ” 
  &&  “ ((y1_pre - y2_pre ) <= 200) ” 
  &&  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre <> y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (IntArray.undef_full out_pre 4 )
.

Definition solver_partial_solve_wit_12 := solver_partial_solve_wit_12_pure -> solver_partial_solve_wit_12_aux.

Definition solver_partial_solve_wit_13 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_full out_pre 4 )
|--
  “ (retval = retval_2) ” 
  &&  “ (retval_2 = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre <> y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre 1 4 )
.

Definition solver_partial_solve_wit_14 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
  **  (IntArray.undef_seg out_pre 1 4 )
|--
  “ (retval = retval_2) ” 
  &&  “ (retval_2 = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre <> y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (1 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
.

Definition solver_partial_solve_wit_15 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (IntArray.undef_seg out_pre (1 + 1 ) 4 )
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  “ (retval = retval_2) ” 
  &&  “ (retval_2 = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre <> y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (2 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre 2 (1 + 1 ) 4 )
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
.

Definition solver_partial_solve_wit_16 := 
forall (out_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval = retval_2)) (PreH2 : (retval_2 = (Z.abs ((y1_pre - y2_pre ))))) (PreH3 : (retval = (Z.abs ((x1_pre - x2_pre ))))) (PreH4 : (y1_pre <> y2_pre)) (PreH5 : (x1_pre <> x2_pre)) (PreH6 : ((-100) <= x1_pre)) (PreH7 : (x1_pre <= 100)) (PreH8 : ((-100) <= y1_pre)) (PreH9 : (y1_pre <= 100)) (PreH10 : ((-100) <= x2_pre)) (PreH11 : (x2_pre <= 100)) (PreH12 : ((-100) <= y2_pre)) (PreH13 : (y2_pre <= 100)) (PreH14 : (Pre x1_pre y1_pre x2_pre y2_pre )) ,
  (IntArray.undef_seg out_pre ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
|--
  “ (retval = retval_2) ” 
  &&  “ (retval_2 = (Z.abs ((y1_pre - y2_pre )))) ” 
  &&  “ (retval = (Z.abs ((x1_pre - x2_pre )))) ” 
  &&  “ (y1_pre <> y2_pre) ” 
  &&  “ (x1_pre <> x2_pre) ” 
  &&  “ ((-100) <= x1_pre) ” 
  &&  “ (x1_pre <= 100) ” 
  &&  “ ((-100) <= y1_pre) ” 
  &&  “ (y1_pre <= 100) ” 
  &&  “ ((-100) <= x2_pre) ” 
  &&  “ (x2_pre <= 100) ” 
  &&  “ ((-100) <= y2_pre) ” 
  &&  “ (y2_pre <= 100) ” 
  &&  “ (Pre x1_pre y1_pre x2_pre y2_pre ) ”
  &&  (((out_pre + (3 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre 3 ((1 + 1 ) + 1 ) 4 )
  **  (((out_pre + (2 * sizeof(INT)))) # Int  |-> x2_pre)
  **  (((out_pre + (1 * sizeof(INT)))) # Int  |-> y2_pre)
  **  (((out_pre + (0 * sizeof(INT)))) # Int  |-> x1_pre)
.

Module Type VC_Correct.


Axiom proof_of_iabs_safety_wit_1 : iabs_safety_wit_1.
Axiom proof_of_iabs_safety_wit_2 : iabs_safety_wit_2.
Axiom proof_of_iabs_return_wit_1 : iabs_return_wit_1.
Axiom proof_of_iabs_return_wit_2 : iabs_return_wit_2.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12_pure : solver_partial_solve_wit_12_pure.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.

End VC_Correct.
