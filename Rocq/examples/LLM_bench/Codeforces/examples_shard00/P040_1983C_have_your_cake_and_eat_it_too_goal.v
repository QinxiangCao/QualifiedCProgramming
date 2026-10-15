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
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_char_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_goal.
From SimpleC.EE.LLM_bench.Codeforces Require Import array2_ext_strategy_proof.

(*----- Function try_order -----*)

Definition try_order_safety_wit_1 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "pos" ) )) # Int  |->_)
  **  (IntArray.full ( &( "right" ) ) 3 (repeat_Z (0) (3)) )
  **  (IntArray.full ( &( "left" ) ) 3 (repeat_Z (0) (3)) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_2 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_3 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_4 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_5 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  (IntArray.full ( &( "left" ) ) 3 (repeat_Z (0) (3)) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_6 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  (IntArray.full ( &( "left" ) ) 3 (repeat_Z (0) (3)) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_7 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  (IntArray.full ( &( "left" ) ) 3 (repeat_Z (0) (3)) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_8 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "part" ) )) # Int  |->_)
  **  ((( &( "pos" ) )) # Int  |-> 0)
  **  (IntArray.full ( &( "right" ) ) 3 (repeat_Z (0) (3)) )
  **  (IntArray.full ( &( "left" ) ) 3 (repeat_Z (0) (3)) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_9 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part <= 2)) (PreH15 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition try_order_safety_wit_10 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights )) ,
  ((( &( "acc" ) )) # Int64  |->_)
  **  ((( &( "start" ) )) # Int  |-> pos)
  **  (IntArray.full order_pre 3 ord )
  **  ((( &( "who" ) )) # Int  |-> (Znth part ord 0))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_11 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
) \/
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
).

Definition try_order_safety_wit_11_split_goal_1 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= INT64_MAX) ”
.

Definition try_order_safety_wit_11_split_goal_2 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((INT64_MIN) <= (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
.

Definition try_order_safety_wit_12 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "acc" ) )) # Int64  |-> (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ))
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition try_order_safety_wit_13 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (who: Z) (start: Z) (acc: Z) (PreH1 : (0 <= part)) (PreH2 : (part < 2)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (0 <= start)) (PreH6 : (start <= n_pre)) (PreH7 : (0 <= acc)) (PreH8 : (acc < need_pre)) (PreH9 : (TryOrderSpec a b c ord None )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> n_pre)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_14 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((start + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + 1 )) ”
.

Definition try_order_safety_wit_15 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition try_order_safety_wit_16 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (IntArray.full ( &( "right" ) ) 3 (replace_Znth (who) (pos) (rights)) )
  **  (IntArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1 )) (lefts)) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "part" ) )) # Int  |-> part)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((part + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (part + 1 )) ”
.

Definition try_order_safety_wit_17 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights )) ,
  ((( &( "who" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition try_order_safety_wit_18 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights )) ,
  ((( &( "acc" ) )) # Int64  |->_)
  **  (IntArray.full order_pre 3 ord )
  **  ((( &( "who" ) )) # Int  |-> (Znth 2 ord 0))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_19 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "acc" ) )) # Int64  |-> (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ))
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition try_order_safety_wit_20 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
) \/
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
).

Definition try_order_safety_wit_20_split_goal_1 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= INT64_MAX) ”
.

Definition try_order_safety_wit_20_split_goal_2 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((INT64_MIN) <= (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
.

Definition try_order_safety_wit_21 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (0 <= acc)) (PreH6 : (acc < need_pre)) (PreH7 : (TryOrderSpec a b c ord None )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_22 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition try_order_safety_wit_23 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition try_order_safety_wit_24 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition try_order_safety_wit_25 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (0 <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH10 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH11 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * i ) 6 )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition try_order_safety_wit_26 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * i ) 6 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition try_order_safety_wit_27 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * i ) 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition try_order_safety_wit_28 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition try_order_safety_wit_29 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition try_order_safety_wit_30 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition try_order_safety_wit_31 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition try_order_safety_wit_32 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 (((2 * i ) + 1 ) + 1 ) (app ((app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z)))))) ((cons ((Znth i rights 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (((2 * i ) + 1 ) + 1 ) 6 )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition try_order_safety_wit_33 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_result: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH8 : ((Zlength (raw_result)) = 6)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "need" ) )) # Int64  |-> need_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "who" ) )) # Int  |-> who)
  **  ((( &( "acc" ) )) # Int64  |-> acc)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.full out_pre 6 raw_result )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition try_order_entail_wit_1 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  (IntArray.full ( &( "right" ) ) 3 (repeat_Z (0) (3)) )
  **  (IntArray.full ( &( "left" ) ) 3 (repeat_Z (0) (3)) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 0 0 lefts rights ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  TT && emp 
|--
  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 0 0 (repeat_Z (0) (3)) (repeat_Z (0) (3)) ) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (1 <= need_pre) ”
  &&  emp
).

Definition try_order_entail_wit_1_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 0 0 (repeat_Z (0) (3)) (repeat_Z (0) (3)) )
.

Definition try_order_entail_wit_1_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  (need_pre <= 200000000000)
.

Definition try_order_entail_wit_1_split_goal_3 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (CakeOrder ord )) (PreH10 : ((Zlength (ord)) = 3)) ,
  (1 <= need_pre)
.

Definition try_order_entail_wit_2 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (IntArray.full order_pre 3 ord )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (row_ptr: Z)  (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ ((Znth part ord 0) = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= (Znth part ord 0)) ” 
  &&  “ ((Znth part ord 0) < 3) ” 
  &&  “ (pos = pos) ” 
  &&  “ (0 = 0) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 (Znth part ord 0) row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + ((Znth part ord 0) * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth ((Znth part ord 0)) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
|--
  EX (row_ptr: Z) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ ((Znth part ord 0) = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= (Znth part ord 0)) ” 
  &&  “ ((Znth part ord 0) < 3) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 (Znth part ord 0) row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + ((Znth part ord 0) * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth ((Znth part ord 0)) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
).

Definition try_order_entail_wit_3 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (row_ptr_2: Z) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) (0)))) (PreH16 : (0 <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = 0)) (PreH20 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (Int64Array.full row_ptr_2 n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (row_ptr: Z)  (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (who = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (start >= 0) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights ) ” 
  &&  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) (0)))) (PreH16 : (0 <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = 0)) (PreH20 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  TT && emp 
|--
  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start start need_pre 0 ) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (start >= 0) ”
  &&  emp
).

Definition try_order_entail_wit_3_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) (0)))) (PreH16 : (0 <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = 0)) (PreH20 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start start need_pre 0 )
.

Definition try_order_entail_wit_3_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) (0)))) (PreH16 : (0 <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = 0)) (PreH20 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (start <= n_pre)
.

Definition try_order_entail_wit_3_split_goal_3 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) (0)))) (PreH16 : (0 <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = 0)) (PreH20 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (0 <= start)
.

Definition try_order_entail_wit_3_split_goal_4 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) (0)))) (PreH16 : (0 <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = 0)) (PreH20 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (start <= n_pre)
.

Definition try_order_entail_wit_3_split_goal_5 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (0 <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) (0)))) (PreH16 : (0 <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = 0)) (PreH20 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (start >= 0)
.

Definition try_order_entail_wit_4 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr_2: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64Array.full row_ptr_2 n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (row_ptr: Z)  (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (who = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (start >= 0) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= n_pre) ” 
  &&  “ (0 <= (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ” 
  &&  “ ((acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights ) ” 
  &&  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start (pos + 1 ) need_pre (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  TT && emp 
|--
  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start (pos + 1 ) need_pre (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) ) ” 
  &&  “ ((acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= 200000000000) ” 
  &&  “ (0 <= (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
  &&  emp
).

Definition try_order_entail_wit_4_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start (pos + 1 ) need_pre (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) )
.

Definition try_order_entail_wit_4_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  ((acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= 200000000000)
.

Definition try_order_entail_wit_4_split_goal_3 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (0 <= (acc + (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ))
.

Definition try_order_entail_wit_5_1 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= 0)) (PreH20 : (start <= n_pre)) (PreH21 : (0 <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : (0 <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH26 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (who = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ ((acc < need_pre) -> (pos >= n_pre)) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights ) ” 
  &&  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= 0)) (PreH20 : (start <= n_pre)) (PreH21 : (0 <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : (0 <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH26 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
).

Definition try_order_entail_wit_5_1_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= 0)) (PreH20 : (start <= n_pre)) (PreH21 : (0 <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : (0 <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH26 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
.

Definition try_order_entail_wit_5_1_split_goal_spatial := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= 0)) (PreH20 : (start <= n_pre)) (PreH21 : (0 <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : (0 <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH26 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
.

Definition try_order_entail_wit_5_2 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (who = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ ((acc < need_pre) -> (pos >= n_pre)) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights ) ” 
  &&  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ (start <= pos) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
).

Definition try_order_entail_wit_5_2_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ (start <= pos) ”
.

Definition try_order_entail_wit_5_2_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
.

Definition try_order_entail_wit_5_2_split_goal_spatial := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
.

Definition try_order_entail_wit_6 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  ((( &( "pos" ) )) # Int  |-> pos)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (rights: (@list Z))  (lefts: (@list Z)) ,
  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc < need_pre) ” 
  &&  “ (TryOrderSpec a b c ord None ) ”
  &&  ((( &( "pos" ) )) # Int  |-> n_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  TT && emp 
|--
  “ (TryOrderSpec a b c ord None ) ” 
  &&  “ (0 <= acc) ”
  &&  emp
).

Definition try_order_entail_wit_6_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (TryOrderSpec a b c ord None )
.

Definition try_order_entail_wit_6_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (0 <= acc)
.

Definition try_order_entail_wit_7 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (IntArray.full ( &( "right" ) ) 3 (replace_Znth (who) (pos) (rights_2)) )
  **  (IntArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1 )) (lefts_2)) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= (part + 1 )) ” 
  &&  “ ((part + 1 ) <= 2) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre (part + 1 ) pos lefts rights ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  TT && emp 
|--
  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre (part + 1 ) pos (replace_Znth (who) ((start + 1 )) (lefts_2)) (replace_Znth (who) (pos) (rights_2)) ) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (1 <= need_pre) ”
  &&  emp
).

Definition try_order_entail_wit_7_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre (part + 1 ) pos (replace_Znth (who) ((start + 1 )) (lefts_2)) (replace_Znth (who) (pos) (rights_2)) )
.

Definition try_order_entail_wit_7_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (need_pre <= 200000000000)
.

Definition try_order_entail_wit_7_split_goal_3 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts_2 rights_2 )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (1 <= need_pre)
.

Definition try_order_entail_wit_8 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (IntArray.full order_pre 3 ord )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (row_ptr: Z)  (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ ((Znth 2 ord 0) = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= (Znth 2 ord 0)) ” 
  &&  “ ((Znth 2 ord 0) < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 (Znth 2 ord 0) row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + ((Znth 2 ord 0) * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth ((Znth 2 ord 0)) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (part: Z) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts_2 rights_2 )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
|--
  EX (row_ptr: Z) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ ((Znth 2 ord 0) = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= (Znth 2 ord 0)) ” 
  &&  “ ((Znth 2 ord 0) < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 (Znth 2 ord 0) row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + ((Znth 2 ord 0) * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth ((Znth 2 ord 0)) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
).

Definition try_order_entail_wit_9 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (row_ptr_2: Z) (who: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (who = (Znth (2) (ord) (0)))) (PreH14 : (0 <= who)) (PreH15 : (who < 3)) (PreH16 : (0 <= pos)) (PreH17 : (pos <= n_pre)) (PreH18 : (acc = 0)) (PreH19 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (Int64Array.full row_ptr_2 n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (row_ptr: Z)  (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (who = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights ) ” 
  &&  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos pos acc ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (who: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (who = (Znth (2) (ord) (0)))) (PreH14 : (0 <= who)) (PreH15 : (who < 3)) (PreH16 : (0 <= pos)) (PreH17 : (pos <= n_pre)) (PreH18 : (acc = 0)) (PreH19 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) ,
  TT && emp 
|--
  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos pos 0 ) ”
  &&  emp
).

Definition try_order_entail_wit_9_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (who: Z) (pos: Z) (acc: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord )) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (who = (Znth (2) (ord) (0)))) (PreH14 : (0 <= who)) (PreH15 : (who < 3)) (PreH16 : (0 <= pos)) (PreH17 : (pos <= n_pre)) (PreH18 : (acc = 0)) (PreH19 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) ,
  (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos pos 0 )
.

Definition try_order_entail_wit_10 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr_2: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64Array.full row_ptr_2 n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr_2)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (row_ptr: Z)  (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (who = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ” 
  &&  “ ((acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights ) ” 
  &&  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos (i + 1 ) (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) ) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  TT && emp 
|--
  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos (i + 1 ) (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) ) ” 
  &&  “ ((acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= 200000000000) ” 
  &&  “ (0 <= (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) )) ”
  &&  emp
).

Definition try_order_entail_wit_10_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos (i + 1 ) (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) )
.

Definition try_order_entail_wit_10_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  ((acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ) <= 200000000000)
.

Definition try_order_entail_wit_10_split_goal_3 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (0 <= (acc + (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0) ))
.

Definition try_order_entail_wit_11 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (who = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights ) ” 
  &&  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc ) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
).

Definition try_order_entail_wit_11_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc ) ”
.

Definition try_order_entail_wit_11_split_goal_2 := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
.

Definition try_order_entail_wit_11_split_goal_spatial := 
forall (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts_2: (@list Z)) (rights_2: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
|--
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
.

Definition try_order_entail_wit_12 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (rights: (@list Z))  (lefts: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc < need_pre) ” 
  &&  “ (TryOrderSpec a b c ord None ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  TT && emp 
|--
  “ (TryOrderSpec a b c ord None ) ”
  &&  emp
).

Definition try_order_entail_wit_12_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  (TryOrderSpec a b c ord None )
.

Definition try_order_entail_wit_13 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  (IntArray.full ( &( "right" ) ) 3 (replace_Znth (who) (n_pre) (rights_2)) )
  **  (IntArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((pos + 1 )) (lefts_2)) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  TT && emp 
|--
  “ (TryOrderSpec a b c ord (Some ((OutputBounds ((replace_Znth (who) ((pos + 1 )) (lefts_2))) ((replace_Znth (who) (n_pre) (rights_2)))))) ) ”
  &&  emp
).

Definition try_order_entail_wit_13_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts_2 rights_2 )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  (TryOrderSpec a b c ord (Some ((OutputBounds ((replace_Znth (who) ((pos + 1 )) (lefts_2))) ((replace_Znth (who) (n_pre) (rights_2)))))) )
.

Definition try_order_entail_wit_14 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (lefts: (@list Z))  (rights: (@list Z))  (raw_prefix: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * 0 )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * 0 ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 ))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * 0 ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * 0 ) 6 )
) \/
(
forall (out_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (raw_prefix: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * 0 )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * 0 ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts_2) (rights_2)) 0) + 1 ))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.seg out_pre 0 (2 * 0 ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * 0 ) 6 )
).

Definition try_order_entail_wit_15 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (raw_prefix_2: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix_2)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix_2 0) = ((Znth j (OutputBounds (lefts_2) (rights_2)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 (((2 * i ) + 1 ) + 1 ) (app ((app (raw_prefix_2) ((cons ((Znth i lefts_2 0)) ((@nil Z)))))) ((cons ((Znth i rights_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (((2 * i ) + 1 ) + 1 ) 6 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
|--
  EX (lefts: (@list Z))  (rights: (@list Z))  (raw_prefix: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * (i + 1 ) )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * (i + 1 ) ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 ))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * (i + 1 ) ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * (i + 1 ) ) 6 )
) \/
(
forall (out_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (raw_prefix_2: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix_2)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix_2 0) = ((Znth j (OutputBounds (lefts_2) (rights_2)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 (((2 * i ) + 1 ) + 1 ) (app ((app (raw_prefix_2) ((cons ((Znth i lefts_2 0)) ((@nil Z)))))) ((cons ((Znth i rights_2 0)) ((@nil Z))))) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
|--
  EX (raw_prefix: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * (i + 1 ) )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * (i + 1 ) ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts_2) (rights_2)) 0) + 1 ))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.seg out_pre 0 (2 * (i + 1 ) ) raw_prefix )
).

Definition try_order_entail_wit_16 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) )) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (2 * i ))) -> ((Znth j_2 raw_prefix 0) = ((Znth j_2 (OutputBounds (lefts_2) (rights_2)) 0) + 1 )))) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts_2 )
  **  (IntArray.full ( &( "right" ) ) 3 rights_2 )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * i ) 6 )
|--
  EX (raw_result: (@list Z))  (lefts: (@list Z))  (rights: (@list Z)) ,
  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ” 
  &&  “ ((Zlength (raw_result)) = 6) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 ))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.full out_pre 6 raw_result )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) )) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (2 * i ))) -> ((Znth j_2 raw_prefix 0) = ((Znth j_2 (OutputBounds (lefts_2) (rights_2)) 0) + 1 )))) ,
  TT && emp 
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts_2) (rights_2)) 0) + 1 ))) ”
  &&  emp
).

Definition try_order_entail_wit_16_split_goal_1 := 
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts_2: (@list Z)) (rights_2: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i >= 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))) )) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < (2 * i ))) -> ((Znth j_2 raw_prefix 0) = ((Znth j_2 (OutputBounds (lefts_2) (rights_2)) 0) + 1 )))) ,
  forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts_2) (rights_2)) 0) + 1 )))
.

Definition try_order_return_wit_1 := 
(
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_result_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH8 : ((Zlength (raw_result_2)) = 6)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result_2 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full out_pre 6 raw_result_2 )
|--
  EX (raw_result: (@list Z))  (result: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (TryOrderSpec a b c ord (Some (result)) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result 0) = ((Znth i result 0) + 1 ))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full out_pre 6 raw_result )
) \/
(
forall (need_pre: Z) (n_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_result_2: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH8 : ((Zlength (raw_result_2)) = 6)) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result_2 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  TT && emp 
|--
  EX (result: (@list Z)) ,
  “ (TryOrderSpec a b c ord (Some (result)) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result_2 0) = ((Znth i result 0) + 1 ))) ”
  &&  emp
).

Definition try_order_return_wit_2 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (0 <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (0 <= acc)) (PreH6 : (acc < need_pre)) (PreH7 : (TryOrderSpec a b c ord None )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 = 0) ” 
  &&  “ (TryOrderSpec a b c ord None ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_return_wit_3 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (part: Z) (who: Z) (start: Z) (acc: Z) (PreH1 : (0 <= part)) (PreH2 : (part < 2)) (PreH3 : (0 <= who)) (PreH4 : (who < 3)) (PreH5 : (0 <= start)) (PreH6 : (start <= n_pre)) (PreH7 : (0 <= acc)) (PreH8 : (acc < need_pre)) (PreH9 : (TryOrderSpec a b c ord None )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 = 0) ” 
  &&  “ (TryOrderSpec a b c ord None ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_1 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (part < 2) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part <= 2) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights ) ”
  &&  (((order_pre + (part * sizeof(INT)))) # Int  |-> (Znth part ord 0))
  **  (IntArray.missing_i order_pre part 0 3 ord )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_2 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (pos: Z) (start: Z) (who: Z) (part: Z) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord )) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : (0 <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) (0)))) (PreH18 : (0 <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= 0)) (PreH21 : (start <= n_pre)) (PreH22 : (0 <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : (0 <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH27 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (acc < need_pre) ” 
  &&  “ (pos < n_pre) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (who = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (start >= 0) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights ) ” 
  &&  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc ) ”
  &&  (((row_ptr + (pos * sizeof(INT64)))) # Int64  |-> (Znth pos (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0))
  **  (Int64Array.missing_i row_ptr pos 0 n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_3 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (acc >= need_pre) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (who = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ ((acc < need_pre) -> (pos >= n_pre)) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights ) ” 
  &&  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc ) ”
  &&  (((( &( "left" ) ) + (who * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "left" ) ) who 0 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_4 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (who: Z) (start: Z) (pos: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (CakeOrder ord )) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : (0 <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights )) (PreH22 : (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc )) ,
  (IntArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1 )) (lefts)) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (acc >= need_pre) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part < 2) ” 
  &&  “ (who = (Znth (part) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ ((acc < need_pre) -> (pos >= n_pre)) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part start lefts rights ) ” 
  &&  “ (SearchPrefixState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who start pos need_pre acc ) ”
  &&  (((( &( "right" ) ) + (who * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "right" ) ) who 0 3 rights )
  **  (IntArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1 )) (lefts)) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_5 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (pos: Z) (lefts: (@list Z)) (rights: (@list Z)) (part: Z) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (part >= 2) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= part) ” 
  &&  “ (part <= 2) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre part pos lefts rights ) ”
  &&  (((order_pre + (2 * sizeof(INT)))) # Int  |-> (Znth 2 ord 0))
  **  (IntArray.missing_i order_pre 2 0 3 ord )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_6 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row_ptr: Z) (lefts: (@list Z)) (rights: (@list Z)) (acc: Z) (i: Z) (pos: Z) (who: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) (0)))) (PreH15 : (0 <= who)) (PreH16 : (who < 3)) (PreH17 : (0 <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : (0 <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH23 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc )) ,
  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (Int64Array.full row_ptr n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (i < n_pre) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (who = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights ) ” 
  &&  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos i acc ) ”
  &&  (((row_ptr + (i * sizeof(INT64)))) # Int64  |-> (Znth i (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) 0))
  **  (Int64Array.missing_i row_ptr i 0 n_pre (Znth (who) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z))) )
  **  (Int64PtrArray2.missing_i v_pre 3 who row_ptr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (who * sizeof(PTR)))) # Ptr  |-> row_ptr)
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_7 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (acc >= need_pre) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (who = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights ) ” 
  &&  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc ) ”
  &&  (((( &( "left" ) ) + (who * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "left" ) ) who 0 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_8 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (pos: Z) (who: Z) (acc: Z) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord )) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (0 <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) (0)))) (PreH17 : (0 <= who)) (PreH18 : (who < 3)) (PreH19 : (0 <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights )) (PreH22 : (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc )) ,
  (IntArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((pos + 1 )) (lefts)) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (acc >= need_pre) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need_pre = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need_pre) ” 
  &&  “ (need_pre <= 200000000000) ” 
  &&  “ (CakeOrder ord ) ” 
  &&  “ ((Zlength (ord)) = 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (who = (Znth (2) (ord) (0))) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (0 <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (GreedyRawState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) ord need_pre 2 pos lefts rights ) ” 
  &&  “ (SuffixSumState (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) who pos n_pre acc ) ”
  &&  (((( &( "right" ) ) + (who * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "right" ) ) who 0 3 rights )
  **  (IntArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((pos + 1 )) (lefts)) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.undef_full out_pre 6 )
.

Definition try_order_partial_solve_wit_9 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * i ) 6 )
|--
  “ (i < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * i )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 ))) ”
  &&  (((( &( "left" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i lefts 0))
  **  (IntArray.missing_i ( &( "left" ) ) i 0 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * i ) 6 )
.

Definition try_order_partial_solve_wit_10 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
  **  (IntArray.undef_seg out_pre (2 * i ) 6 )
|--
  “ (i < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * i )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 ))) ”
  &&  (((out_pre + ((2 * i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 (2 * i ) raw_prefix )
.

Definition try_order_partial_solve_wit_11 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
|--
  “ (i < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * i )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 ))) ”
  &&  (((( &( "right" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth i rights 0))
  **  (IntArray.missing_i ( &( "right" ) ) i 0 3 rights )
  **  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
.

Definition try_order_partial_solve_wit_12 := 
forall (out_pre: Z) (order_pre: Z) (need_pre: Z) (n_pre: Z) (v_pre: Z) (ord: (@list Z)) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (lefts: (@list Z)) (rights: (@list Z)) (raw_prefix: (@list Z)) (i: Z) (acc: Z) (who: Z) (pos: Z) (PreH1 : (i < 3)) (PreH2 : (0 <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : (0 <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : (0 <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i ))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) )) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 )))) ,
  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((2 * i ) + 1 ) 6 )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
|--
  “ (i < 3) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= n_pre) ” 
  &&  “ (0 <= who) ” 
  &&  “ (who < 3) ” 
  &&  “ (need_pre <= acc) ” 
  &&  “ (acc <= 200000000000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 3) ” 
  &&  “ ((Zlength (raw_prefix)) = (2 * i )) ” 
  &&  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (2 * i ))) -> ((Znth j raw_prefix 0) = ((Znth j (OutputBounds (lefts) (rights)) 0) + 1 ))) ”
  &&  (((out_pre + (((2 * i ) + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (((2 * i ) + 1 ) + 1 ) 6 )
  **  (IntArray.full ( &( "right" ) ) 3 rights )
  **  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (raw_prefix) ((cons ((Znth i lefts 0)) ((@nil Z))))) )
  **  (IntArray.full ( &( "left" ) ) 3 lefts )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full order_pre 3 ord )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((repeat_Z (0) (1)))))))))))))))))))))))))))))))))))) )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_20 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = 0)) ,
  ((( &( "row0" ) )) # Ptr  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0)
  **  (Int64Array.full row0 n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "row0" ) )) # Ptr  |-> row0)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0)
  **  (Int64Array.full row0 n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_22 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64Array.full row0_addr n_pre a )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> (total + (Znth i a 0) ))
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_23 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64Array.full row0_addr n_pre a )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ ((total + (Znth i a 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (Znth i a 0) )) ”
) \/
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64Array.full row0_addr n_pre a )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ ((total + (Znth i a 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (Znth i a 0) )) ”
).

Definition solver_safety_wit_23_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64Array.full row0_addr n_pre a )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ ((total + (Znth i a 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_23_split_goal_2 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64Array.full row0_addr n_pre a )
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ ((INT64_MIN) <= (total + (Znth i a 0) )) ”
.

Definition solver_safety_wit_24 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (((total + 2 ) <> (INT64_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition solver_safety_wit_25 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ ((total + 2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + 2 )) ”
.

Definition solver_safety_wit_26 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_27 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_28 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "z" ) )) # Int  |->_)
  **  ((( &( "need" ) )) # Int64  |-> ((total + 2 ) ÷ 3 ))
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_29 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (z: Z) (need: Z) (total: Z) (row0_addr: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need)) (PreH11 : (need <= 200000000000)) (PreH12 : (0 <= z)) (PreH13 : (z <= 6)) (PreH14 : (OrderTable table )) (PreH15 : (FailedOrders a b c z )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition solver_safety_wit_30 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (z: Z) (need: Z) (total: Z) (row0_addr: Z) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table )) (PreH16 : (FailedOrders a b c z )) ,
  ((( &( "ordp" ) )) # Ptr  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
|--
  “ ((3 * z ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (3 * z )) ”
.

Definition solver_safety_wit_31 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (z: Z) (need: Z) (total: Z) (row0_addr: Z) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table )) (PreH16 : (FailedOrders a b c z )) ,
  ((( &( "ordp" ) )) # Ptr  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_32 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (z: Z) (need: Z) (total: Z) (row0_addr: Z) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table )) (PreH16 : (FailedOrders a b c z )) ,
  ((( &( "ordp" ) )) # Ptr  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_33 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (z: Z) (ordp: Z) (raw_result: (@list Z)) (result: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result)) )) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result 0) = ((Znth i result 0) + 1 )))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH9 : (Pre a b c )) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : (0 <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z )) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH19 : (OrderTable table )) (PreH20 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH21 : ((Zlength (before)) = (3 * z ))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH24 : (OrderAt z (OrderFor (z)) )) (PreH25 : (CakeOrder (OrderFor (z)) )) (PreH26 : (retval = 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.full out_pre 6 raw_result )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ordp" ) )) # Ptr  |-> ordp)
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ False ”
.

Definition solver_safety_wit_34 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (z: Z) (ordp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None )) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : (0 <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z )) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH18 : (OrderTable table )) (PreH19 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH20 : ((Zlength (before)) = (3 * z ))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH23 : (OrderAt z (OrderFor (z)) )) (PreH24 : (CakeOrder (OrderFor (z)) )) (PreH25 : (retval <> 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.undef_full out_pre 6 )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ordp" ) )) # Ptr  |-> ordp)
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ False ”
.

Definition solver_safety_wit_35 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (result: (@list Z)) (raw_result: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (z: Z) (ok: Z) (ordp: Z) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH3 : (0 <= z)) (PreH4 : (z < 6)) (PreH5 : (ok = 1)) (PreH6 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH7 : (Spec a b c (Some (result)) )) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result 0) = ((Znth j result 0) + 1 )))) (PreH9 : (OrderTable table )) (PreH10 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH11 : ((Zlength (before)) = (3 * z ))) (PreH12 : ((Zlength ((OrderFor (z)))) = 3)) (PreH13 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  ((( &( "ordp" ) )) # Ptr  |-> ordp)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full out_pre 6 raw_result )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (z: Z) (ok: Z) (ordp: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c )) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : (0 <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = 0)) (PreH14 : (OrderTable table )) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH16 : (FailedOrders a b c (z + 1 ) )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition solver_safety_wit_37 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH3 : (FailedOrders a b c 6 )) (PreH4 : (Spec a b c None )) (PreH5 : (OrderTable table )) ,
  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((repeat_Z (0) (1)))))))))))))))))))))))))))))))))))) )
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  EX (row0: Z) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (0 = 0) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 0 row0 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0)
  **  (Int64Array.full row0 n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
) \/
(
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
|--
  EX (row0: Z) ,
  “ ((cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((repeat_Z (0) (1)))))))))))))))))))))))))))))))))))) = (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z)))))))))))))))))))))))))))))))))))))) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 0 row0 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0)
  **  (Int64Array.full row0 n_pre a )
).

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0: Z) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = 0)) ,
  (Int64PtrArray2.missing_i v_pre 3 0 row0 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0)
  **  (Int64Array.full row0 n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (total = (sum ((sublist (0) (0) (a))))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 200000000000) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 0 row0 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0)
  **  (Int64Array.full row0 n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
) \/
(
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = 0)) ,
  TT && emp 
|--
  “ (0 = (sum ((sublist (0) (0) (a))))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = 0)) ,
  (0 = (sum ((sublist (0) (0) (a)))))
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64Array.full row0_addr n_pre a )
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((total + (Znth i a 0) ) = (sum ((sublist (0) ((i + 1 )) (a))))) ” 
  &&  “ (0 <= (total + (Znth i a 0) )) ” 
  &&  “ ((total + (Znth i a 0) ) <= 200000000000) ”
  &&  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (Int64Array.full row0_addr n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
) \/
(
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  TT && emp 
|--
  “ ((total + (Znth i a 0) ) <= 200000000000) ” 
  &&  “ (0 <= (total + (Znth i a 0) )) ” 
  &&  “ ((total + (Znth i a 0) ) = (sum ((sublist (0) ((i + 1 )) (a))))) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  ((total + (Znth i a 0) ) <= 200000000000)
.

Definition solver_entail_wit_3_split_goal_2 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (0 <= (total + (Znth i a 0) ))
.

Definition solver_entail_wit_3_split_goal_3 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  ((total + (Znth i a 0) ) = (sum ((sublist (0) ((i + 1 )) (a)))))
.

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (Int64Array.full row0_addr n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 200000000000) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
) \/
(
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (Int64Array.full row0_addr n_pre a )
|--
  “ (total = (sum (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (Int64Array.full row0_addr n_pre a )
|--
  “ (total = (sum (a))) ”
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (Int64Array.full row0_addr n_pre a )
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
.

Definition solver_entail_wit_4_split_goal_spatial := 
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (Int64Array.full row0_addr n_pre a )
|--
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
.

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  EX (table: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (((total + 2 ) ÷ 3 ) = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= ((total + 2 ) ÷ 3 )) ” 
  &&  “ (((total + 2 ) ÷ 3 ) <= 200000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 6) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (FailedOrders a b c 0 ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
) \/
(
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  TT && emp 
|--
  “ (FailedOrders a b c 0 ) ” 
  &&  “ (OrderTable (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) ) ” 
  &&  “ (((total + 2 ) ÷ 3 ) <= 200000000000) ” 
  &&  “ (1 <= ((total + 2 ) ÷ 3 )) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  (FailedOrders a b c 0 )
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  (OrderTable (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  (((total + 2 ) ÷ 3 ) <= 200000000000)
.

Definition solver_entail_wit_5_split_goal_4 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (total: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (0 <= total)) (PreH10 : (total <= 200000000000)) ,
  (1 <= ((total + 2 ) ÷ 3 ))
.

Definition solver_entail_wit_6 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (z: Z) (need: Z) (total: Z) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2 )) (PreH16 : (FailedOrders a b c z )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table_2 )
|--
  EX (before: (@list Z))  (after: (@list Z))  (table: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (FailedOrders a b c z ) ” 
  &&  “ ((( &( "orders" ) ) + ((3 * z ) * sizeof(INT))) = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (table = (app (before) ((app ((OrderFor (z))) (after))))) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ” 
  &&  “ (OrderAt z (OrderFor (z)) ) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.full (( &( "orders" ) ) + ((3 * z ) * sizeof(INT))) 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
) \/
(
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (z: Z) (need: Z) (total: Z) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2 )) (PreH16 : (FailedOrders a b c z )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "orders" ) ) 18 table_2 )
|--
  EX (before: (@list Z))  (after: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (FailedOrders a b c z ) ” 
  &&  “ ((( &( "orders" ) ) + ((3 * z ) * sizeof(INT))) = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (OrderTable (app (before) ((app ((OrderFor (z))) (after)))) ) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ” 
  &&  “ (OrderAt z (OrderFor (z)) ) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.full (( &( "orders" ) ) + ((3 * z ) * sizeof(INT))) 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
).

Definition solver_entail_wit_7_1 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None )) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : (0 <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z )) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH18 : (OrderTable table )) (PreH19 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH20 : ((Zlength (before)) = (3 * z ))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH23 : (OrderAt z (OrderFor (z)) )) (PreH24 : (CakeOrder (OrderFor (z)) )) (PreH25 : (retval = 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ (retval = 0) ” 
  &&  “ (TryOrderSpec a b c (OrderFor (z)) None ) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (FailedOrders a b c z ) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (table = (app (before) ((app ((OrderFor (z))) (after))))) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ” 
  &&  “ (OrderAt z (OrderFor (z)) ) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ” 
  &&  “ (retval = 0) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
.

Definition solver_entail_wit_7_2 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (raw_result: (@list Z)) (result: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result)) )) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result 0) = ((Znth i result 0) + 1 )))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH9 : (Pre a b c )) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : (0 <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z )) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH19 : (OrderTable table )) (PreH20 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH21 : ((Zlength (before)) = (3 * z ))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH24 : (OrderAt z (OrderFor (z)) )) (PreH25 : (CakeOrder (OrderFor (z)) )) (PreH26 : (retval = 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.full out_pre 6 raw_result )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ (retval = 0) ” 
  &&  “ (TryOrderSpec a b c (OrderFor (z)) None ) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (FailedOrders a b c z ) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (table = (app (before) ((app ((OrderFor (z))) (after))))) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ” 
  &&  “ (OrderAt z (OrderFor (z)) ) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ” 
  &&  “ (retval = 0) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
.

Definition solver_entail_wit_8_1 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None )) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : (0 <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z )) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH18 : (OrderTable table )) (PreH19 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH20 : ((Zlength (before)) = (3 * z ))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH23 : (OrderAt z (OrderFor (z)) )) (PreH24 : (CakeOrder (OrderFor (z)) )) (PreH25 : (retval <> 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  EX (raw_result: (@list Z))  (result: (@list Z)) ,
  “ (retval = 1) ” 
  &&  “ (TryOrderSpec a b c (OrderFor (z)) (Some (result)) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result 0) = ((Znth i result 0) + 1 ))) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (FailedOrders a b c z ) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (table = (app (before) ((app ((OrderFor (z))) (after))))) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ” 
  &&  “ (OrderAt z (OrderFor (z)) ) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ” 
  &&  “ (retval <> 0) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.full out_pre 6 raw_result )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
.

Definition solver_entail_wit_8_2 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (raw_result: (@list Z)) (result: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result)) )) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result 0) = ((Znth i result 0) + 1 )))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH9 : (Pre a b c )) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : (0 <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z )) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH19 : (OrderTable table )) (PreH20 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH21 : ((Zlength (before)) = (3 * z ))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH24 : (OrderAt z (OrderFor (z)) )) (PreH25 : (CakeOrder (OrderFor (z)) )) (PreH26 : (retval <> 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.full out_pre 6 raw_result )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ (retval = 1) ” 
  &&  “ (TryOrderSpec a b c (OrderFor (z)) (Some (result)) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result 0) = ((Znth i result 0) + 1 ))) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (FailedOrders a b c z ) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (table = (app (before) ((app ((OrderFor (z))) (after))))) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ” 
  &&  “ (OrderAt z (OrderFor (z)) ) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ” 
  &&  “ (retval <> 0) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.full out_pre 6 raw_result )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
.

Definition solver_entail_wit_9 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (before_2: (@list Z)) (after_2: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (raw_result_2: (@list Z)) (result_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result_2)) )) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result_2 0) = ((Znth i result_2 0) + 1 )))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH9 : (Pre a b c )) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : (0 <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z )) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH19 : (OrderTable table_2 )) (PreH20 : (table_2 = (app (before_2) ((app ((OrderFor (z))) (after_2)))))) (PreH21 : ((Zlength (before_2)) = (3 * z ))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after_2)) = (18 - (3 * (z + 1 ) ) ))) (PreH24 : (OrderAt z (OrderFor (z)) )) (PreH25 : (CakeOrder (OrderFor (z)) )) (PreH26 : (retval <> 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.full out_pre 6 raw_result_2 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before_2 )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after_2 )
|--
  EX (before: (@list Z))  (after: (@list Z))  (table: (@list Z))  (raw_result: (@list Z))  (result: (@list Z)) ,
  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (retval = 1) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (Spec a b c (Some (result)) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result 0) = ((Znth j result 0) + 1 ))) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (table = (app (before) ((app ((OrderFor (z))) (after))))) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full out_pre 6 raw_result )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
) \/
(
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (before_2: (@list Z)) (after_2: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (raw_result_2: (@list Z)) (result_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result_2)) )) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result_2 0) = ((Znth i result_2 0) + 1 )))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH9 : (Pre a b c )) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : (0 <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z )) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH19 : (OrderTable table_2 )) (PreH20 : (table_2 = (app (before_2) ((app ((OrderFor (z))) (after_2)))))) (PreH21 : ((Zlength (before_2)) = (3 * z ))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after_2)) = (18 - (3 * (z + 1 ) ) ))) (PreH24 : (OrderAt z (OrderFor (z)) )) (PreH25 : (CakeOrder (OrderFor (z)) )) (PreH26 : (retval <> 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before_2 )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after_2 )
|--
  EX (before: (@list Z))  (after: (@list Z))  (result: (@list Z)) ,
  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (retval = 1) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (Spec a b c (Some (result)) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result_2 0) = ((Znth j result 0) + 1 ))) ” 
  &&  “ (OrderTable (app (before) ((app ((OrderFor (z))) (after)))) ) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "orders" ) ) 18 (app (before) ((app ((OrderFor (z))) (after)))) )
).

Definition solver_entail_wit_10 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (before: (@list Z)) (after: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None )) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : (0 <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z )) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH18 : (OrderTable table_2 )) (PreH19 : (table_2 = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH20 : ((Zlength (before)) = (3 * z ))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH23 : (OrderAt z (OrderFor (z)) )) (PreH24 : (CakeOrder (OrderFor (z)) )) (PreH25 : (retval = 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  EX (table: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (retval = 0) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (FailedOrders a b c (z + 1 ) ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
) \/
(
forall (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (before: (@list Z)) (after: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None )) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH8 : (Pre a b c )) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : (0 <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z )) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH18 : (OrderTable table_2 )) (PreH19 : (table_2 = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH20 : ((Zlength (before)) = (3 * z ))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH23 : (OrderAt z (OrderFor (z)) )) (PreH24 : (CakeOrder (OrderFor (z)) )) (PreH25 : (retval = 0)) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  EX (table: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (retval = 0) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (FailedOrders a b c (z + 1 ) ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
).

Definition solver_entail_wit_11 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (total: Z) (need: Z) (z: Z) (ok: Z) (ordp: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c )) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : (0 <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = 0)) (PreH14 : (OrderTable table_2 )) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH16 : (FailedOrders a b c (z + 1 ) )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= 6) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (FailedOrders a b c (z + 1 ) ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
) \/
(
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (total: Z) (need: Z) (z: Z) (ok: Z) (ordp: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c )) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : (0 <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = 0)) (PreH14 : (OrderTable table_2 )) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH16 : (FailedOrders a b c (z + 1 ) )) ,
  TT && emp 
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (total: Z) (need: Z) (z: Z) (ok: Z) (ordp: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c )) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : (0 <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = 0)) (PreH14 : (OrderTable table_2 )) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH16 : (FailedOrders a b c (z + 1 ) )) ,
  forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))
.

Definition solver_entail_wit_12 := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (z: Z) (need: Z) (total: Z) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2 )) (PreH16 : (FailedOrders a b c z )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table_2 )
|--
  EX (table: (@list Z)) ,
  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (FailedOrders a b c 6 ) ” 
  &&  “ (Spec a b c None ) ” 
  &&  “ (OrderTable table ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 table )
) \/
(
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (z: Z) (need: Z) (total: Z) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2 )) (PreH16 : (FailedOrders a b c z )) ,
  TT && emp 
|--
  “ (Spec a b c None ) ” 
  &&  “ (FailedOrders a b c 6 ) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (z: Z) (need: Z) (total: Z) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2 )) (PreH16 : (FailedOrders a b c z )) ,
  (Spec a b c None )
.

Definition solver_entail_wit_12_split_goal_2 := 
forall (n_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table_2: (@list Z)) (z: Z) (need: Z) (total: Z) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : (0 <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2 )) (PreH16 : (FailedOrders a b c z )) ,
  (FailedOrders a b c 6 )
.

Definition solver_return_wit_1 := 
forall (out_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (total: Z) (need: Z) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH3 : (FailedOrders a b c 6 )) (PreH4 : (Spec a b c None )) (PreH5 : (OrderTable table )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
|--
  “ (0 = 0) ” 
  &&  “ (Spec a b c None ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
.

Definition solver_return_wit_2 := 
(
forall (out_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (result_2: (@list Z)) (raw_result_2: (@list Z)) (total: Z) (need: Z) (z: Z) (ok: Z) (ordp: Z) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH3 : (0 <= z)) (PreH4 : (z < 6)) (PreH5 : (ok = 1)) (PreH6 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH7 : (Spec a b c (Some (result_2)) )) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result_2 0) = ((Znth j result_2 0) + 1 )))) (PreH9 : (OrderTable table )) (PreH10 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH11 : ((Zlength (before)) = (3 * z ))) (PreH12 : ((Zlength ((OrderFor (z)))) = 3)) (PreH13 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full out_pre 6 raw_result_2 )
|--
  EX (raw_result: (@list Z))  (result: (@list Z)) ,
  “ (1 = 1) ” 
  &&  “ (Spec a b c (Some (result)) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result 0) = ((Znth i result 0) + 1 ))) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full out_pre 6 raw_result )
) \/
(
forall (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (result_2: (@list Z)) (raw_result_2: (@list Z)) (total: Z) (need: Z) (z: Z) (ok: Z) (ordp: Z) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH3 : (0 <= z)) (PreH4 : (z < 6)) (PreH5 : (ok = 1)) (PreH6 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH7 : (Spec a b c (Some (result_2)) )) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < 6)) -> ((Znth j raw_result_2 0) = ((Znth j result_2 0) + 1 )))) (PreH9 : (OrderTable table )) (PreH10 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH11 : ((Zlength (before)) = (3 * z ))) (PreH12 : ((Zlength ((OrderFor (z)))) = 3)) (PreH13 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) ,
  TT && emp 
|--
  EX (result: (@list Z)) ,
  “ (Spec a b c (Some (result)) ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 6)) -> ((Znth i raw_result_2 0) = ((Znth i result 0) + 1 ))) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (row0_addr: Z) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH7 : (Pre a b c )) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist (0) (i) (a)))))) (PreH12 : (0 <= total)) (PreH13 : (total <= 200000000000)) ,
  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (Int64Array.full row0_addr n_pre a )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
|--
  “ (i < n_pre) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (total = (sum ((sublist (0) (i) (a))))) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= 200000000000) ”
  &&  (((row0_addr + (i * sizeof(INT64)))) # Int64  |-> (Znth i a 0))
  **  (Int64Array.missing_i row0_addr i 0 n_pre a )
  **  (Int64PtrArray2.missing_i v_pre 3 0 row0_addr (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (((v_pre + (0 * sizeof(PTR)))) # Ptr  |-> row0_addr)
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.full ( &( "orders" ) ) 18 (cons (0) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (1) ((cons (1) ((cons (0) ((cons (2) ((cons (1) ((cons (2) ((cons (0) ((cons (2) ((cons (0) ((cons (1) ((cons (2) ((cons (1) ((cons (0) ((@nil Z))))))))))))))))))))))))))))))))))))) )
.

Definition solver_partial_solve_wit_2_pure := 
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (z: Z) (ordp: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need)) (PreH11 : (need <= 200000000000)) (PreH12 : (0 <= z)) (PreH13 : (z < 6)) (PreH14 : (FailedOrders a b c z )) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH16 : (OrderTable table )) (PreH17 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH18 : ((Zlength (before)) = (3 * z ))) (PreH19 : ((Zlength ((OrderFor (z)))) = 3)) (PreH20 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH21 : (OrderAt z (OrderFor (z)) )) (PreH22 : (CakeOrder (OrderFor (z)) )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ordp" ) )) # Ptr  |-> ordp)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ”
) \/
(
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (z: Z) (ordp: Z) (PreH1 : (need <= INT64_MAX)) (PreH2 : (total <= INT64_MAX)) (PreH3 : (need >= INT64_MIN)) (PreH4 : (total >= INT64_MIN)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (z >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (3 <= (Zlength (a)))) (PreH10 : ((Zlength (a)) <= 200000)) (PreH11 : ((Zlength (b)) = (Zlength (a)))) (PreH12 : ((Zlength (c)) = (Zlength (a)))) (PreH13 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH14 : (Pre a b c )) (PreH15 : (n_pre = (Zlength (a)))) (PreH16 : (total = (sum (a)))) (PreH17 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH18 : (1 <= need)) (PreH19 : (need <= 200000000000)) (PreH20 : (0 <= z)) (PreH21 : (z < 6)) (PreH22 : (FailedOrders a b c z )) (PreH23 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH24 : (OrderTable table )) (PreH25 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH26 : ((Zlength (before)) = (3 * z ))) (PreH27 : ((Zlength ((OrderFor (z)))) = 3)) (PreH28 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH29 : (OrderAt z (OrderFor (z)) )) (PreH30 : (CakeOrder (OrderFor (z)) )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ordp" ) )) # Ptr  |-> ordp)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (row0_addr: Z) (total: Z) (need: Z) (z: Z) (ordp: Z) (PreH1 : (need <= INT64_MAX)) (PreH2 : (total <= INT64_MAX)) (PreH3 : (need >= INT64_MIN)) (PreH4 : (total >= INT64_MIN)) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (z >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (3 <= (Zlength (a)))) (PreH10 : ((Zlength (a)) <= 200000)) (PreH11 : ((Zlength (b)) = (Zlength (a)))) (PreH12 : ((Zlength (c)) = (Zlength (a)))) (PreH13 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH14 : (Pre a b c )) (PreH15 : (n_pre = (Zlength (a)))) (PreH16 : (total = (sum (a)))) (PreH17 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH18 : (1 <= need)) (PreH19 : (need <= 200000000000)) (PreH20 : (0 <= z)) (PreH21 : (z < 6)) (PreH22 : (FailedOrders a b c z )) (PreH23 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH24 : (OrderTable table )) (PreH25 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH26 : ((Zlength (before)) = (3 * z ))) (PreH27 : ((Zlength ((OrderFor (z)))) = 3)) (PreH28 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH29 : (OrderAt z (OrderFor (z)) )) (PreH30 : (CakeOrder (OrderFor (z)) )) ,
  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "v" ) )) # Ptr  |-> v_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "row0" ) )) # Ptr  |-> row0_addr)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  ((( &( "need" ) )) # Int64  |-> need)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  ((( &( "ordp" ) )) # Ptr  |-> ordp)
  **  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (out_pre: Z) (n_pre: Z) (v_pre: Z) (c: (@list Z)) (b: (@list Z)) (a: (@list Z)) (table: (@list Z)) (before: (@list Z)) (after: (@list Z)) (total: Z) (need: Z) (z: Z) (ordp: Z) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000)))) (PreH6 : (Pre a b c )) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (need = (((sum (a)) + 2 ) ÷ 3 ))) (PreH10 : (1 <= need)) (PreH11 : (need <= 200000000000)) (PreH12 : (0 <= z)) (PreH13 : (z < 6)) (PreH14 : (FailedOrders a b c z )) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) ))) (PreH16 : (OrderTable table )) (PreH17 : (table = (app (before) ((app ((OrderFor (z))) (after)))))) (PreH18 : ((Zlength (before)) = (3 * z ))) (PreH19 : ((Zlength ((OrderFor (z)))) = 3)) (PreH20 : ((Zlength (after)) = (18 - (3 * (z + 1 ) ) ))) (PreH21 : (OrderAt z (OrderFor (z)) )) (PreH22 : (CakeOrder (OrderFor (z)) )) ,
  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
|--
  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row: Z) , forall (col: Z) , (((((0 <= row) /\ (row < 3)) /\ (0 <= col)) /\ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col) ((Znth (row) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ (3 <= (Zlength (a))) ” 
  &&  “ ((Zlength (a)) <= 200000) ” 
  &&  “ ((Zlength (b)) = (Zlength (a))) ” 
  &&  “ ((Zlength (c)) = (Zlength (a))) ” 
  &&  “ forall (row_2: Z) , forall (col_2: Z) , (((((0 <= row_2) /\ (row_2 < 3)) /\ (0 <= col_2)) /\ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0))) /\ ((Znth (col_2) ((Znth (row_2) ((cons (a) ((cons (b) ((cons (c) ((@nil (@list Z))))))))) ((@nil Z)))) (0)) <= 1000000))) ” 
  &&  “ (Pre a b c ) ” 
  &&  “ (n_pre = (Zlength (a))) ” 
  &&  “ (total = (sum (a))) ” 
  &&  “ (need = (((sum (a)) + 2 ) ÷ 3 )) ” 
  &&  “ (1 <= need) ” 
  &&  “ (need <= 200000000000) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z < 6) ” 
  &&  “ (FailedOrders a b c z ) ” 
  &&  “ (ordp = (( &( "orders" ) ) + ((3 * z ) * sizeof(INT) ) )) ” 
  &&  “ (OrderTable table ) ” 
  &&  “ (table = (app (before) ((app ((OrderFor (z))) (after))))) ” 
  &&  “ ((Zlength (before)) = (3 * z )) ” 
  &&  “ ((Zlength ((OrderFor (z)))) = 3) ” 
  &&  “ ((Zlength (after)) = (18 - (3 * (z + 1 ) ) )) ” 
  &&  “ (OrderAt z (OrderFor (z)) ) ” 
  &&  “ (CakeOrder (OrderFor (z)) ) ”
  &&  (Int64PtrArray2.full v_pre 3 (cons (a) ((cons (b) ((cons (c) ((@nil (@list Z)))))))) )
  **  (IntArray.full ordp 3 (OrderFor (z)) )
  **  (IntArray.undef_full out_pre 6 )
  **  (IntArray.seg ( &( "orders" ) ) 0 (3 * z ) before )
  **  (IntArray.seg ( &( "orders" ) ) (3 * (z + 1 ) ) 18 after )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

Axiom proof_of_try_order_safety_wit_1 : try_order_safety_wit_1.
Axiom proof_of_try_order_safety_wit_2 : try_order_safety_wit_2.
Axiom proof_of_try_order_safety_wit_3 : try_order_safety_wit_3.
Axiom proof_of_try_order_safety_wit_4 : try_order_safety_wit_4.
Axiom proof_of_try_order_safety_wit_5 : try_order_safety_wit_5.
Axiom proof_of_try_order_safety_wit_6 : try_order_safety_wit_6.
Axiom proof_of_try_order_safety_wit_7 : try_order_safety_wit_7.
Axiom proof_of_try_order_safety_wit_8 : try_order_safety_wit_8.
Axiom proof_of_try_order_safety_wit_9 : try_order_safety_wit_9.
Axiom proof_of_try_order_safety_wit_10 : try_order_safety_wit_10.
Axiom proof_of_try_order_safety_wit_11 : try_order_safety_wit_11.
Axiom proof_of_try_order_safety_wit_12 : try_order_safety_wit_12.
Axiom proof_of_try_order_safety_wit_13 : try_order_safety_wit_13.
Axiom proof_of_try_order_safety_wit_14 : try_order_safety_wit_14.
Axiom proof_of_try_order_safety_wit_15 : try_order_safety_wit_15.
Axiom proof_of_try_order_safety_wit_16 : try_order_safety_wit_16.
Axiom proof_of_try_order_safety_wit_17 : try_order_safety_wit_17.
Axiom proof_of_try_order_safety_wit_18 : try_order_safety_wit_18.
Axiom proof_of_try_order_safety_wit_19 : try_order_safety_wit_19.
Axiom proof_of_try_order_safety_wit_20 : try_order_safety_wit_20.
Axiom proof_of_try_order_safety_wit_21 : try_order_safety_wit_21.
Axiom proof_of_try_order_safety_wit_22 : try_order_safety_wit_22.
Axiom proof_of_try_order_safety_wit_23 : try_order_safety_wit_23.
Axiom proof_of_try_order_safety_wit_24 : try_order_safety_wit_24.
Axiom proof_of_try_order_safety_wit_25 : try_order_safety_wit_25.
Axiom proof_of_try_order_safety_wit_26 : try_order_safety_wit_26.
Axiom proof_of_try_order_safety_wit_27 : try_order_safety_wit_27.
Axiom proof_of_try_order_safety_wit_28 : try_order_safety_wit_28.
Axiom proof_of_try_order_safety_wit_29 : try_order_safety_wit_29.
Axiom proof_of_try_order_safety_wit_30 : try_order_safety_wit_30.
Axiom proof_of_try_order_safety_wit_31 : try_order_safety_wit_31.
Axiom proof_of_try_order_safety_wit_32 : try_order_safety_wit_32.
Axiom proof_of_try_order_safety_wit_33 : try_order_safety_wit_33.
Axiom proof_of_try_order_entail_wit_1 : try_order_entail_wit_1.
Axiom proof_of_try_order_entail_wit_2 : try_order_entail_wit_2.
Axiom proof_of_try_order_entail_wit_3 : try_order_entail_wit_3.
Axiom proof_of_try_order_entail_wit_4 : try_order_entail_wit_4.
Axiom proof_of_try_order_entail_wit_5_1 : try_order_entail_wit_5_1.
Axiom proof_of_try_order_entail_wit_5_2 : try_order_entail_wit_5_2.
Axiom proof_of_try_order_entail_wit_6 : try_order_entail_wit_6.
Axiom proof_of_try_order_entail_wit_7 : try_order_entail_wit_7.
Axiom proof_of_try_order_entail_wit_8 : try_order_entail_wit_8.
Axiom proof_of_try_order_entail_wit_9 : try_order_entail_wit_9.
Axiom proof_of_try_order_entail_wit_10 : try_order_entail_wit_10.
Axiom proof_of_try_order_entail_wit_11 : try_order_entail_wit_11.
Axiom proof_of_try_order_entail_wit_12 : try_order_entail_wit_12.
Axiom proof_of_try_order_entail_wit_13 : try_order_entail_wit_13.
Axiom proof_of_try_order_entail_wit_14 : try_order_entail_wit_14.
Axiom proof_of_try_order_entail_wit_15 : try_order_entail_wit_15.
Axiom proof_of_try_order_entail_wit_16 : try_order_entail_wit_16.
Axiom proof_of_try_order_return_wit_1 : try_order_return_wit_1.
Axiom proof_of_try_order_return_wit_2 : try_order_return_wit_2.
Axiom proof_of_try_order_return_wit_3 : try_order_return_wit_3.
Axiom proof_of_try_order_partial_solve_wit_1 : try_order_partial_solve_wit_1.
Axiom proof_of_try_order_partial_solve_wit_2 : try_order_partial_solve_wit_2.
Axiom proof_of_try_order_partial_solve_wit_3 : try_order_partial_solve_wit_3.
Axiom proof_of_try_order_partial_solve_wit_4 : try_order_partial_solve_wit_4.
Axiom proof_of_try_order_partial_solve_wit_5 : try_order_partial_solve_wit_5.
Axiom proof_of_try_order_partial_solve_wit_6 : try_order_partial_solve_wit_6.
Axiom proof_of_try_order_partial_solve_wit_7 : try_order_partial_solve_wit_7.
Axiom proof_of_try_order_partial_solve_wit_8 : try_order_partial_solve_wit_8.
Axiom proof_of_try_order_partial_solve_wit_9 : try_order_partial_solve_wit_9.
Axiom proof_of_try_order_partial_solve_wit_10 : try_order_partial_solve_wit_10.
Axiom proof_of_try_order_partial_solve_wit_11 : try_order_partial_solve_wit_11.
Axiom proof_of_try_order_partial_solve_wit_12 : try_order_partial_solve_wit_12.
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
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.

End VC_Correct.
