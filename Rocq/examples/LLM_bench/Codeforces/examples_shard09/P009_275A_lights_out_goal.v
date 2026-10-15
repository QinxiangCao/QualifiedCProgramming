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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P009_275A_lights_out_lib.
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

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
  **  (IntArray.full ( &( "dj" ) ) 5 (app ((repeat_Z (0) (3))) ((cons ((-1)) ((cons (1) ((@nil Z))))))) )
  **  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray2.full press_pre 3 3 g )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH3 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH4 : (0 <= i)) (PreH5 : (i <= 3)) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH3 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH4 : (0 <= i)) (PreH5 : (i < 3)) (PreH6 : (0 <= j)) (PreH7 : (j <= 3)) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_17 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  ((( &( "tog" ) )) # Int  |->_)
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "tog" ) )) # Int  |-> 0)
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH3 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH4 : (0 <= i)) (PreH5 : (i < 3)) (PreH6 : (0 <= j)) (PreH7 : (j < 3)) (PreH8 : (0 <= d)) (PreH9 : (d <= 5)) (PreH10 : (0 <= tog)) (PreH11 : (tog <= 500)) (PreH12 : (TogglePrefix g i j d tog )) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition solver_safety_wit_20 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |->_)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((j + (Znth d lights_dj 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + (Znth d lights_dj 0) )) ”
) \/
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |->_)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((j + (Znth d lights_dj 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + (Znth d lights_dj 0) )) ”
).

Definition solver_safety_wit_20_split_goal_1 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |->_)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((j + (Znth d lights_dj 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_20_split_goal_2 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |->_)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((INT_MIN) <= (j + (Znth d lights_dj 0) )) ”
.

Definition solver_safety_wit_21 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |->_)
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((i + (Znth d lights_di 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + (Znth d lights_di 0) )) ”
) \/
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |->_)
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((i + (Znth d lights_di 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + (Znth d lights_di 0) )) ”
).

Definition solver_safety_wit_21_split_goal_1 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |->_)
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((i + (Znth d lights_di 0) ) <= INT_MAX) ”
.

Definition solver_safety_wit_21_split_goal_2 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |->_)
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((INT_MIN) <= (i + (Znth d lights_di 0) )) ”
.

Definition solver_safety_wit_22 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_23 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH2 : (d < 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_24 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) < 3)) (PreH2 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH3 : (d < 5)) (PreH4 : ((Zlength (g)) = 3)) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH6 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) (PreH9 : (0 <= j)) (PreH10 : (j < 3)) (PreH11 : (0 <= d)) (PreH12 : (d <= 5)) (PreH13 : (0 <= tog)) (PreH14 : (tog <= 500)) (PreH15 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH2 : ((i + (Znth d lights_di 0) ) < 3)) (PreH3 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH4 : (d < 5)) (PreH5 : ((Zlength (g)) = 3)) (PreH6 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH7 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH8 : (0 <= i)) (PreH9 : (i < 3)) (PreH10 : (0 <= j)) (PreH11 : (j < 3)) (PreH12 : (0 <= d)) (PreH13 : (d <= 5)) (PreH14 : (0 <= tog)) (PreH15 : (tog <= 500)) (PreH16 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_26 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray2.full press_pre 3 3 g )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) )) ”
) \/
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray2.full press_pre 3 3 g )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) )) ”
).

Definition solver_safety_wit_26_split_goal_1 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray2.full press_pre 3 3 g )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) <= INT_MAX) ”
.

Definition solver_safety_wit_26_split_goal_2 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray2.full press_pre 3 3 g )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  ((( &( "nj" ) )) # Int  |-> (j + (Znth d lights_dj 0) ))
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "ni" ) )) # Int  |-> (i + (Znth d lights_di 0) ))
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((INT_MIN) <= (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) )) ”
.

Definition solver_safety_wit_27 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray2.full press_pre 3 3 g )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ))
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_28 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 0)) (PreH2 : ((i + (Znth d lights_di 0) ) < 3)) (PreH3 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH4 : (d < 5)) (PreH5 : ((Zlength (g)) = 3)) (PreH6 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH7 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH8 : (0 <= i)) (PreH9 : (i < 3)) (PreH10 : (0 <= j)) (PreH11 : (j < 3)) (PreH12 : (0 <= d)) (PreH13 : (d <= 5)) (PreH14 : (0 <= tog)) (PreH15 : (tog <= 500)) (PreH16 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) < 0)) (PreH2 : (d < 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) >= 3)) (PreH2 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH3 : (d < 5)) (PreH4 : ((Zlength (g)) = 3)) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH6 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) (PreH9 : (0 <= j)) (PreH10 : (j < 3)) (PreH11 : (0 <= d)) (PreH12 : (d <= 5)) (PreH13 : (0 <= tog)) (PreH14 : (tog <= 500)) (PreH15 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_31 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) >= 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_32 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d >= 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((tog <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_33 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d >= 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_34 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d >= 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "tog" ) )) # Int  |-> tog)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_35 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_36 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) <> 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (0))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_37 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) = 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (1))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
  **  ((( &( "press" ) )) # Ptr  |-> press_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
  **  (IntArray.full ( &( "dj" ) ) 5 (app ((repeat_Z (0) (3))) ((cons ((-1)) ((cons (1) ((@nil Z))))))) )
  **  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  (IntArray2.full press_pre 3 3 g )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * 0 ))) )
) \/
(
forall (out_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ ((app ((repeat_Z (0) (3))) ((cons ((-1)) ((cons (1) ((@nil Z))))))) = lights_dj) ” 
  &&  “ ((cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) = lights_di) ”
  &&  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * 0 ))) )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (out_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ”
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (out_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (out_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
|--
  “ ((app ((repeat_Z (0) (3))) ((cons ((-1)) ((cons (1) ((@nil Z))))))) = lights_dj) ”
.

Definition solver_entail_wit_1_split_goal_4 := 
forall (out_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
|--
  “ ((cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) = lights_di) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (out_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * 0 ))) )
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + 0 ))) )
) \/
(
forall (out_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
  &&  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + 0 ))) )
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (out_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ”
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (out_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
.

Definition solver_entail_wit_2_split_goal_spatial := 
forall (out_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + 0 ))) )
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 5) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 500) ” 
  &&  “ (TogglePrefix g i j 0 0 ) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
) \/
(
forall (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  TT && emp 
|--
  “ (TogglePrefix g i j 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j < 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  (TogglePrefix g i j 0 0 )
.

Definition solver_entail_wit_4_1 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray2.full press_pre 3 3 g )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 5) ” 
  &&  “ (0 <= (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) )) ” 
  &&  “ ((tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) <= 500) ” 
  &&  “ (TogglePrefix g i j (d + 1 ) (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) ) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
) \/
(
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  TT && emp 
|--
  “ (TogglePrefix g i j (d + 1 ) (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) ) ” 
  &&  “ ((tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) <= 500) ” 
  &&  “ (0 <= (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) )) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 := 
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (TogglePrefix g i j (d + 1 ) (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) )
.

Definition solver_entail_wit_4_1_split_goal_2 := 
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  ((tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ) <= 500)
.

Definition solver_entail_wit_4_1_split_goal_3 := 
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (0 <= (tog + (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)) ))
.

Definition solver_entail_wit_4_2 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 0)) (PreH2 : ((i + (Znth d lights_di 0) ) < 3)) (PreH3 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH4 : (d < 5)) (PreH5 : ((Zlength (g)) = 3)) (PreH6 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH7 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH8 : (0 <= i)) (PreH9 : (i < 3)) (PreH10 : (0 <= j)) (PreH11 : (j < 3)) (PreH12 : (0 <= d)) (PreH13 : (d <= 5)) (PreH14 : (0 <= tog)) (PreH15 : (tog <= 500)) (PreH16 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
) \/
(
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 0)) (PreH2 : ((i + (Znth d lights_di 0) ) < 3)) (PreH3 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH4 : (d < 5)) (PreH5 : ((Zlength (g)) = 3)) (PreH6 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH7 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH8 : (0 <= i)) (PreH9 : (i < 3)) (PreH10 : (0 <= j)) (PreH11 : (j < 3)) (PreH12 : (0 <= d)) (PreH13 : (d <= 5)) (PreH14 : (0 <= tog)) (PreH15 : (tog <= 500)) (PreH16 : (TogglePrefix g i j d tog )) ,
  TT && emp 
|--
  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 := 
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 0)) (PreH2 : ((i + (Znth d lights_di 0) ) < 3)) (PreH3 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH4 : (d < 5)) (PreH5 : ((Zlength (g)) = 3)) (PreH6 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH7 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH8 : (0 <= i)) (PreH9 : (i < 3)) (PreH10 : (0 <= j)) (PreH11 : (j < 3)) (PreH12 : (0 <= d)) (PreH13 : (d <= 5)) (PreH14 : (0 <= tog)) (PreH15 : (tog <= 500)) (PreH16 : (TogglePrefix g i j d tog )) ,
  (TogglePrefix g i j (d + 1 ) tog )
.

Definition solver_entail_wit_4_3 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) < 0)) (PreH2 : (d < 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
) \/
(
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) < 0)) (PreH2 : (d < 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  TT && emp 
|--
  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  emp
).

Definition solver_entail_wit_4_3_split_goal_1 := 
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) < 0)) (PreH2 : (d < 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (TogglePrefix g i j (d + 1 ) tog )
.

Definition solver_entail_wit_4_4 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) >= 3)) (PreH2 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH3 : (d < 5)) (PreH4 : ((Zlength (g)) = 3)) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH6 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) (PreH9 : (0 <= j)) (PreH10 : (j < 3)) (PreH11 : (0 <= d)) (PreH12 : (d <= 5)) (PreH13 : (0 <= tog)) (PreH14 : (tog <= 500)) (PreH15 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
) \/
(
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) >= 3)) (PreH2 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH3 : (d < 5)) (PreH4 : ((Zlength (g)) = 3)) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH6 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) (PreH9 : (0 <= j)) (PreH10 : (j < 3)) (PreH11 : (0 <= d)) (PreH12 : (d <= 5)) (PreH13 : (0 <= tog)) (PreH14 : (tog <= 500)) (PreH15 : (TogglePrefix g i j d tog )) ,
  TT && emp 
|--
  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  emp
).

Definition solver_entail_wit_4_4_split_goal_1 := 
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((i + (Znth d lights_di 0) ) >= 3)) (PreH2 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH3 : (d < 5)) (PreH4 : ((Zlength (g)) = 3)) (PreH5 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH6 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH7 : (0 <= i)) (PreH8 : (i < 3)) (PreH9 : (0 <= j)) (PreH10 : (j < 3)) (PreH11 : (0 <= d)) (PreH12 : (d <= 5)) (PreH13 : (0 <= tog)) (PreH14 : (tog <= 500)) (PreH15 : (TogglePrefix g i j d tog )) ,
  (TogglePrefix g i j (d + 1 ) tog )
.

Definition solver_entail_wit_4_5 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) >= 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
) \/
(
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) >= 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  TT && emp 
|--
  “ (TogglePrefix g i j (d + 1 ) tog ) ”
  &&  emp
).

Definition solver_entail_wit_4_5_split_goal_1 := 
forall (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) >= 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (TogglePrefix g i j (d + 1 ) tog )
.

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 3) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * (i + 1 ) ))) )
) \/
(
forall (out_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
  &&  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * (i + 1 ) ))) )
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (out_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ”
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (out_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
.

Definition solver_entail_wit_5_split_goal_spatial := 
forall (out_pre: Z) (g: (@list (@list Z))) (j: Z) (i: Z)  __default__List_Z (PreH1 : (j >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH4 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j <= 3)) ,
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * (i + 1 ) ))) )
.

Definition solver_entail_wit_6_1 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) <> 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (0))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 3) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + (j + 1 ) ))) )
) \/
(
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) <> 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (0))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
  &&  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + (j + 1 ) ))) )
).

Definition solver_entail_wit_6_1_split_goal_1 := 
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) <> 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (0))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ”
.

Definition solver_entail_wit_6_1_split_goal_2 := 
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) <> 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (0))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
.

Definition solver_entail_wit_6_1_split_goal_spatial := 
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) <> 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (0))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + (j + 1 ) ))) )
.

Definition solver_entail_wit_6_2 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) = 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (1))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= 3) ”
  &&  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + (j + 1 ) ))) )
) \/
(
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) = 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (1))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
  &&  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + (j + 1 ) ))) )
).

Definition solver_entail_wit_6_2_split_goal_1 := 
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) = 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (1))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ”
.

Definition solver_entail_wit_6_2_split_goal_2 := 
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) = 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (1))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ”
.

Definition solver_entail_wit_6_2_split_goal_spatial := 
forall (out_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) = 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r_3: Z) , (((0 <= r_3) /\ (r_3 < 3)) -> ((Zlength ((Znth r_3 g __default__List_Z))) = 3))) (PreH5 : forall (r_4: Z) , forall (c_2: Z) , (((((0 <= r_4) /\ (r_4 < 3)) /\ (0 <= c_2)) /\ (c_2 < 3)) -> ((0 <= (Znth c_2 (Znth r_4 g __default__List_Z) 0)) /\ ((Znth c_2 (Znth r_4 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray2.mixed_full out_pre 3 3 (Array2.replace_mixed_row (i) ((replace_Znth (j) ((Some (1))) ((Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z)))) ((staged_output (g) (((3 * i ) + j ))))) )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + (j + 1 ) ))) )
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) ((3 * i ))) )
|--
  EX (out_spec: (@list (@list Z))) ,
  “ (Spec g out_spec ) ”
  &&  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.full out_pre 3 3 out_spec )
) \/
(
forall (g: (@list (@list Z))) (i: Z)  __default__List_Z (PreH1 : (i >= 3)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i <= 3)) ,
  TT && emp 
|--
  EX (out_spec: (@list (@list Z))) ,
  “ ((staged_output (g) ((3 * i ))) = (Array2.some_rows (out_spec))) ” 
  &&  “ (Spec g out_spec ) ”
  &&  emp
).

Definition solver_partial_solve_wit_1 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z)))  __default__List_Z (PreH1 : ((Zlength (g)) = 3)) (PreH2 : forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3))) (PreH3 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100))))) ,
  (IntArray.full ( &( "dj" ) ) 5 (app ((repeat_Z (0) (3))) ((cons ((-1)) ((cons (1) ((@nil Z))))))) )
  **  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.undef_full out_pre 3 3 )
|--
  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < 3)) -> ((Zlength ((Znth i g __default__List_Z))) = 3)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < 3)) -> forall (k: Z) , (((0 <= k) /\ (k < 3)) -> ((0 <= (Znth k (Znth i_2 g __default__List_Z) 0)) /\ ((Znth k (Znth i_2 g __default__List_Z) 0) <= 100)))) ”
  &&  (IntArray2.undef_full out_pre 3 3 )
  **  (IntArray.full ( &( "dj" ) ) 5 (app ((repeat_Z (0) (3))) ((cons ((-1)) ((cons (1) ((@nil Z))))))) )
  **  (IntArray.full ( &( "di" ) ) 5 (cons (0) ((cons ((-1)) ((cons (1) ((repeat_Z (0) (2)))))))) )
  **  (IntArray2.full press_pre 3 3 g )
.

Definition solver_partial_solve_wit_2 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (d < 5) ” 
  &&  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j d tog ) ”
  &&  (((( &( "dj" ) ) + (d * sizeof(INT)))) # Int  |-> (Znth d lights_dj 0))
  **  (IntArray.missing_i ( &( "dj" ) ) d 0 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
.

Definition solver_partial_solve_wit_3 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : (d < 5)) (PreH2 : ((Zlength (g)) = 3)) (PreH3 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH4 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH5 : (0 <= i)) (PreH6 : (i < 3)) (PreH7 : (0 <= j)) (PreH8 : (j < 3)) (PreH9 : (0 <= d)) (PreH10 : (d <= 5)) (PreH11 : (0 <= tog)) (PreH12 : (tog <= 500)) (PreH13 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ (d < 5) ” 
  &&  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j d tog ) ”
  &&  (((( &( "di" ) ) + (d * sizeof(INT)))) # Int  |-> (Znth d lights_di 0))
  **  (IntArray.missing_i ( &( "di" ) ) d 0 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z (PreH1 : ((j + (Znth d lights_dj 0) ) < 3)) (PreH2 : ((j + (Znth d lights_dj 0) ) >= 0)) (PreH3 : ((i + (Znth d lights_di 0) ) < 3)) (PreH4 : ((i + (Znth d lights_di 0) ) >= 0)) (PreH5 : (d < 5)) (PreH6 : ((Zlength (g)) = 3)) (PreH7 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH8 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH9 : (0 <= i)) (PreH10 : (i < 3)) (PreH11 : (0 <= j)) (PreH12 : (j < 3)) (PreH13 : (0 <= d)) (PreH14 : (d <= 5)) (PreH15 : (0 <= tog)) (PreH16 : (tog <= 500)) (PreH17 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((j + (Znth d lights_dj 0) ) < 3) ” 
  &&  “ ((j + (Znth d lights_dj 0) ) >= 0) ” 
  &&  “ ((i + (Znth d lights_di 0) ) < 3) ” 
  &&  “ ((i + (Znth d lights_di 0) ) >= 0) ” 
  &&  “ (d < 5) ” 
  &&  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j d tog ) ”
  &&  ((((press_pre + ((i + (Znth d lights_di 0) ) * (sizeof(INT) * 3))) + ((j + (Znth d lights_dj 0) ) * sizeof(INT)))) # Int  |-> (Znth ((j + (Znth d lights_dj 0) )) ((Znth (i + (Znth d lights_di 0) ) g __default__List_Z)) (0)))
  **  (IntArray.missing_i (press_pre + ((i + (Znth d lights_di 0) ) * (sizeof(INT) * 3))) (j + (Znth d lights_dj 0) ) 0 3 (Znth (i + (Znth d lights_di 0) ) g __default__List_Z) )
  **  (IntArray2.missing_i press_pre (i + (Znth d lights_di 0) ) 0 3 3 g )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) <> 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((tog % ( 2 ) ) <> 0) ” 
  &&  “ (d >= 5) ” 
  &&  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j d tog ) ”
  &&  ((((out_pre + (i * (sizeof(INT) * 3))) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (out_pre + (i * (sizeof(INT) * 3))) j 0 3 (Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i out_pre i 0 3 3 (staged_output (g) (((3 * i ) + j ))) )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
.

Definition solver_partial_solve_wit_6 := 
forall (out_pre: Z) (press_pre: Z) (g: (@list (@list Z))) (tog: Z) (d: Z) (j: Z) (i: Z)  __default__List_Z  __default__List__App_option_Z (PreH1 : ((tog % ( 2 ) ) = 0)) (PreH2 : (d >= 5)) (PreH3 : ((Zlength (g)) = 3)) (PreH4 : forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3))) (PreH5 : forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100)))) (PreH6 : (0 <= i)) (PreH7 : (i < 3)) (PreH8 : (0 <= j)) (PreH9 : (j < 3)) (PreH10 : (0 <= d)) (PreH11 : (d <= 5)) (PreH12 : (0 <= tog)) (PreH13 : (tog <= 500)) (PreH14 : (TogglePrefix g i j d tog )) ,
  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
  **  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (((3 * i ) + j ))) )
|--
  “ ((tog % ( 2 ) ) = 0) ” 
  &&  “ (d >= 5) ” 
  &&  “ ((Zlength (g)) = 3) ” 
  &&  “ forall (r: Z) , (((0 <= r) /\ (r < 3)) -> ((Zlength ((Znth r g __default__List_Z))) = 3)) ” 
  &&  “ forall (r_2: Z) , forall (c: Z) , (((((0 <= r_2) /\ (r_2 < 3)) /\ (0 <= c)) /\ (c < 3)) -> ((0 <= (Znth c (Znth r_2 g __default__List_Z) 0)) /\ ((Znth c (Znth r_2 g __default__List_Z) 0) <= 100))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 3) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < 3) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 5) ” 
  &&  “ (0 <= tog) ” 
  &&  “ (tog <= 500) ” 
  &&  “ (TogglePrefix g i j d tog ) ”
  &&  ((((out_pre + (i * (sizeof(INT) * 3))) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i (out_pre + (i * (sizeof(INT) * 3))) j 0 3 (Znth i (staged_output (g) (((3 * i ) + j ))) __default__List__App_option_Z) )
  **  (IntArray2.mixed_missing_i out_pre i 0 3 3 (staged_output (g) (((3 * i ) + j ))) )
  **  (IntArray.full ( &( "di" ) ) 5 lights_di )
  **  (IntArray.full ( &( "dj" ) ) 5 lights_dj )
  **  (IntArray2.full press_pre 3 3 g )
.

Definition solver_which_implies_wit_1 := 
(
forall (out_pre: Z) (g: (@list (@list Z))) ,
  (IntArray2.undef_full out_pre 3 3 )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
) \/
(
forall (out_pre: Z) (g: (@list (@list Z))) ,
  (IntArray2.undef_full out_pre 3 3 )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
).

Definition solver_which_implies_wit_1_split_goal_spatial := 
forall (out_pre: Z) (g: (@list (@list Z))) ,
  (IntArray2.undef_full out_pre 3 3 )
|--
  (IntArray2.mixed_full out_pre 3 3 (staged_output (g) (0)) )
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include array2_char_Strategy_Correct.
Include int_array_Strategy_Correct.
Include char_array_Strategy_Correct.
Include array2_ext_Strategy_Correct.

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
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Axiom proof_of_solver_entail_wit_4_5 : solver_entail_wit_4_5.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.

End VC_Correct.
