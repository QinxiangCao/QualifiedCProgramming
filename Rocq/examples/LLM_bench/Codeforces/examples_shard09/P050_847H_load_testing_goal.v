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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P050_847H_load_testing_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full inc_pre n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full inc_pre n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((inc_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 values 0))
  **  (Int64Array.undef_seg inc_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 (i + 1 ) (app (inc_values) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 (i + 1 ) (app (inc_values) ((cons (((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values)) = i)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values)) = i)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values)) = i)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values)) = i)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.undef_seg dec_pre 0 (n_pre - 1 ) )
  **  (((dec_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - 1 ) values 0))
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((n_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition solver_safety_wit_19 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.undef_seg dec_pre 0 (n_pre - 1 ) )
  **  (((dec_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - 1 ) values 0))
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_20 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((-1) <= i)) (PreH8 : (i <= (n_pre - 2 ))) (PreH9 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH12 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_21 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) > ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.undef_seg dec_pre 0 i )
  **  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_22 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.undef_seg dec_pre 0 i )
  **  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_25 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 )) ”
.

Definition solver_safety_wit_28 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_31 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_32 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth 0 inc_values 0) - (Znth 0 values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth 0 inc_values 0) - (Znth 0 values 0) )) ”
.

Definition solver_safety_wit_33 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_34 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_35 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 inc_values 0) - (Znth 0 values 0) ))
  **  (Int64Array.undef_seg pre_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_36 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values) ((cons (((Znth ((i - 1 ) - 0 ) pre_values 0) + ((Znth i inc_values 0) - (Znth i values 0) ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_37 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth ((i - 1 ) - 0 ) pre_values 0) + ((Znth i inc_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i - 1 ) - 0 ) pre_values 0) + ((Znth i inc_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_38 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth i inc_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i inc_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_39 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_40 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_41 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_42 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_43 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (((Znth (n_pre - 1 ) dec_values 0) - (Znth (n_pre - 1 ) values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth (n_pre - 1 ) dec_values 0) - (Znth (n_pre - 1 ) values 0) )) ”
.

Definition solver_safety_wit_44 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_45 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_46 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_47 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_48 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.undef_seg suf_pre 0 (n_pre - 1 ) )
  **  (((suf_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> ((Znth (n_pre - 1 ) dec_values 0) - (Znth (n_pre - 1 ) values 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
|--
  “ ((n_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition solver_safety_wit_49 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.undef_seg suf_pre 0 (n_pre - 1 ) )
  **  (((suf_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> ((Znth (n_pre - 1 ) dec_values 0) - (Znth (n_pre - 1 ) values 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_50 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : ((-1) <= i)) (PreH12 : (i <= (n_pre - 2 ))) (PreH13 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH14 : (PartialSuffixCosts values dec_values suf_values )) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_51 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.undef_seg suf_pre 0 i )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> ((Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) + ((Znth i dec_values 0) - (Znth i values 0) ) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_52 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
|--
  “ (((Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) + ((Znth i dec_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((i + 1 ) - (i + 1 ) ) suf_values 0) + ((Znth i dec_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_53 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
|--
  “ (((Znth i dec_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i dec_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_54 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_55 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_56 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (suf_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : ((Zlength (suf_values)) = n_pre)) (PreH12 : (SuffixCosts values dec_values suf_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  ((( &( "best" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition solver_safety_wit_57 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (suf_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : ((Zlength (suf_values)) = n_pre)) (PreH12 : (SuffixCosts values dec_values suf_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  ((( &( "best" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_58 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (suf_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : ((Zlength (suf_values)) = n_pre)) (PreH12 : (SuffixCosts values dec_values suf_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int64  |-> (-1))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_59 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i inc_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i inc_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_60 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((Znth i inc_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i inc_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_61 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_62 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((Znth i dec_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i dec_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_63 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_64 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((Znth i inc_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i inc_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_65 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (((Znth i pre_values 0) + (Znth i suf_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i pre_values 0) + (Znth i suf_values 0) )) ”
.

Definition solver_safety_wit_66 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i dec_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i dec_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_67 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((Znth i dec_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i dec_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_68 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_69 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((Znth i dec_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i dec_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_70 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) )) ”
.

Definition solver_safety_wit_71 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (((Znth i inc_values 0) - (Znth i values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i inc_values 0) - (Znth i values 0) )) ”
.

Definition solver_safety_wit_72 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |->_)
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
  **  (Int64Array.full a_pre n_pre values )
|--
  “ (((Znth i pre_values 0) + (Znth i suf_values 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth i pre_values 0) + (Znth i suf_values 0) )) ”
.

Definition solver_safety_wit_73 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |-> (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i inc_values 0) - (Znth i values 0) ) ))
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i inc_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_74 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "cost" ) )) # Int64  |-> (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i dec_values 0) - (Znth i values 0) ) ))
  **  ((( &( "peak" ) )) # Int64  |-> (Znth i dec_values 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_75 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : ((Zlength (dec_values)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : ((Zlength (pre_values)) = n_pre)) (PreH13 : (PrefixCosts values inc_values pre_values )) (PreH14 : ((Zlength (suf_values)) = n_pre)) (PreH15 : (SuffixCosts values dec_values suf_values )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i dec_values 0) - (Znth i values 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_76 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : ((Zlength (dec_values)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : ((Zlength (pre_values)) = n_pre)) (PreH13 : (PrefixCosts values inc_values pre_values )) (PreH14 : ((Zlength (suf_values)) = n_pre)) (PreH15 : (SuffixCosts values dec_values suf_values )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i inc_values 0) - (Znth i values 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_77 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i inc_values 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : ((Zlength (dec_values)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : ((Zlength (pre_values)) = n_pre)) (PreH14 : (PrefixCosts values inc_values pre_values )) (PreH15 : ((Zlength (suf_values)) = n_pre)) (PreH16 : (SuffixCosts values dec_values suf_values )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i inc_values 0) - (Znth i values 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_78 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i dec_values 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : ((Zlength (dec_values)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : ((Zlength (pre_values)) = n_pre)) (PreH14 : (PrefixCosts values inc_values pre_values )) (PreH15 : ((Zlength (suf_values)) = n_pre)) (PreH16 : (SuffixCosts values dec_values suf_values )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> (((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i dec_values 0) - (Znth i values 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_79 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i inc_values 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : ((Zlength (dec_values)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : ((Zlength (pre_values)) = n_pre)) (PreH14 : (PrefixCosts values inc_values pre_values )) (PreH15 : ((Zlength (suf_values)) = n_pre)) (PreH16 : (SuffixCosts values dec_values suf_values )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_80 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((((((Znth i pre_values 0) + (Znth i suf_values 0) ) - ((Znth i inc_values 0) - (Znth i values 0) ) ) - ((Znth i dec_values 0) - (Znth i values 0) ) ) + ((Znth i dec_values 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : ((Zlength (dec_values)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : ((Zlength (pre_values)) = n_pre)) (PreH14 : (PrefixCosts values inc_values pre_values )) (PreH15 : ((Zlength (suf_values)) = n_pre)) (PreH16 : (SuffixCosts values dec_values suf_values )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "inc" ) )) # Ptr  |-> inc_pre)
  **  ((( &( "dec" ) )) # Ptr  |-> dec_pre)
  **  ((( &( "pre" ) )) # Ptr  |-> pre_pre)
  **  ((( &( "suf" ) )) # Ptr  |-> suf_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int64  |-> best)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (((inc_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 values 0))
  **  (Int64Array.undef_seg inc_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = 1) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 1)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 1 inc_values )
  **  (Int64Array.undef_seg inc_pre 1 n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (inc_pre: Z) (n_pre: Z) (values: (@list Z)) (PreH1 : ((Znth 0 values 0) <= INT64_MAX)) (PreH2 : ((Znth 0 values 0) >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH6 : (n_pre = (Zlength (values)))) ,
  (((inc_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 values 0))
|--
  EX (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = 1) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 1)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (Int64Array.seg inc_pre 0 1 inc_values )
).

Definition solver_entail_wit_2_1 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 (i + 1 ) (app (inc_values_2) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = (i + 1 )) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 (i + 1 ) inc_values )
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  TT && emp 
|--
  “ (LeftProfilePrefix values (app (inc_values_2) ((cons ((Znth i values 0)) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (inc_values_2) ((cons ((Znth i values 0)) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  (LeftProfilePrefix values (app (inc_values_2) ((cons ((Znth i values 0)) ((@nil Z))))) )
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  ((Zlength ((app (inc_values_2) ((cons ((Znth i values 0)) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_2_2 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 (i + 1 ) (app (inc_values_2) ((cons (((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 )) ((@nil Z))))) )
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = (i + 1 )) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 (i + 1 ) inc_values )
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  TT && emp 
|--
  “ (LeftProfilePrefix values (app (inc_values_2) ((cons (((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 )) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (inc_values_2) ((cons (((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 )) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  (LeftProfilePrefix values (app (inc_values_2) ((cons (((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 )) ((@nil Z))))) )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values_2)) = i)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) ,
  ((Zlength ((app (inc_values_2) ((cons (((Znth ((i - 1 ) - 0 ) inc_values_2 0) + 1 )) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_3 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values_2)) = i)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 i inc_values_2 )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (inc_pre: Z) (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values_2)) = i)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values_2 )
|--
  EX (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (Int64Array.full inc_pre n_pre inc_values )
).

Definition solver_entail_wit_4 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)))) ,
  (Int64Array.undef_seg dec_pre 0 (n_pre - 1 ) )
  **  (((dec_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - 1 ) values 0))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - (n_pre - 2 ) ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 ((n_pre - 2 ) + 1 ) )
  **  (Int64Array.seg dec_pre ((n_pre - 2 ) + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (dec_pre: Z) (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((Znth (n_pre - 1 ) values 0) <= INT64_MAX)) (PreH2 : ((Znth (n_pre - 1 ) values 0) >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values_2)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values_2 )) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)))) ,
  (((dec_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - 1 ) values 0))
|--
  EX (dec_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - (n_pre - 2 ) ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.seg dec_pre ((n_pre - 2 ) + 1 ) n_pre dec_values )
).

Definition solver_entail_wit_5_1 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values_2: (@list Z)) (i: Z) (inc_values_2: (@list Z)) (PreH1 : ((Znth i values 0) > ((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values_2)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values_2 )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values_2)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values_2)))) -> ((1 <= (Znth k_3 dec_values_2 0)) /\ ((Znth k_3 dec_values_2 0) <= 1000100000)))) ,
  (Int64Array.undef_seg dec_pre 0 i )
  **  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - (i - 1 ) ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 ((i - 1 ) + 1 ) )
  **  (Int64Array.seg dec_pre ((i - 1 ) + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (dec_pre: Z) (n_pre: Z) (values: (@list Z)) (dec_values_2: (@list Z)) (i: Z) (inc_values_2: (@list Z)) (PreH1 : ((Znth i values 0) <= INT64_MAX)) (PreH2 : ((Znth i values 0) >= INT64_MIN)) (PreH3 : ((Znth i values 0) > ((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((-1) <= i)) (PreH12 : (i <= (n_pre - 2 ))) (PreH13 : ((Zlength (dec_values_2)) = ((n_pre - i ) - 1 ))) (PreH14 : (RightProfileSuffix values dec_values_2 )) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values_2)))) -> ((1 <= (Znth k_3 dec_values_2 0)) /\ ((Znth k_3 dec_values_2 0) <= 1000100000)))) ,
  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values_2 )
|--
  EX (dec_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - (i - 1 ) ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.seg dec_pre ((i - 1 ) + 1 ) n_pre dec_values )
).

Definition solver_entail_wit_5_2 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values_2: (@list Z)) (i: Z) (inc_values_2: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values_2)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values_2 )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values_2)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values_2)))) -> ((1 <= (Znth k_3 dec_values_2 0)) /\ ((Znth k_3 dec_values_2 0) <= 1000100000)))) ,
  (Int64Array.undef_seg dec_pre 0 i )
  **  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> ((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ))
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values_2 )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - (i - 1 ) ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 ((i - 1 ) + 1 ) )
  **  (Int64Array.seg dec_pre ((i - 1 ) + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (dec_pre: Z) (n_pre: Z) (values: (@list Z)) (dec_values_2: (@list Z)) (i: Z) (inc_values_2: (@list Z)) (PreH1 : (((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ) <= INT64_MAX)) (PreH2 : (((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ) >= INT64_MIN)) (PreH3 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ))) (PreH4 : (i >= 0)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((-1) <= i)) (PreH12 : (i <= (n_pre - 2 ))) (PreH13 : ((Zlength (dec_values_2)) = ((n_pre - i ) - 1 ))) (PreH14 : (RightProfileSuffix values dec_values_2 )) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)))) (PreH16 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values_2)))) -> ((1 <= (Znth k_3 dec_values_2 0)) /\ ((Znth k_3 dec_values_2 0) <= 1000100000)))) ,
  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> ((Znth ((i + 1 ) - (i + 1 ) ) dec_values_2 0) + 1 ))
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values_2 )
|--
  EX (dec_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - (i - 1 ) ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.seg dec_pre ((i - 1 ) + 1 ) n_pre dec_values )
).

Definition solver_entail_wit_6 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values_2: (@list Z)) (i: Z) (inc_values_2: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values_2)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)))) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (Zlength (dec_values_2)))) -> ((1 <= (Znth k_6 dec_values_2 0)) /\ ((Znth k_6 dec_values_2 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values_2 )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (dec_pre: Z) (n_pre: Z) (values: (@list Z)) (dec_values_2: (@list Z)) (i: Z) (inc_values_2: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values_2)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)))) (PreH13 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < (Zlength (dec_values_2)))) -> ((1 <= (Znth k_6 dec_values_2 0)) /\ ((Znth k_6 dec_values_2 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values_2 )
|--
  EX (dec_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (Int64Array.full dec_pre n_pre dec_values )
).

Definition solver_entail_wit_7 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : ((Zlength (dec_values_2)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values_2 )) (PreH9 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)))) (PreH10 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 dec_values_2 0)) /\ ((Znth k_6 dec_values_2 0) <= 1000100000)))) ,
  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 inc_values_2 0) - (Znth 0 values 0) ))
  **  (Int64Array.undef_seg pre_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = 1) ” 
  &&  “ (PartialPrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 1)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg pre_pre 0 1 pre_values )
  **  (Int64Array.undef_seg pre_pre 1 n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (pre_pre: Z) (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (PreH1 : (((Znth 0 inc_values_2 0) - (Znth 0 values 0) ) <= INT64_MAX)) (PreH2 : (((Znth 0 inc_values_2 0) - (Znth 0 values 0) ) >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values_2)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values_2 )) (PreH9 : ((Zlength (dec_values_2)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values_2 )) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)))) (PreH12 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((1 <= (Znth k_6 dec_values_2 0)) /\ ((Znth k_6 dec_values_2 0) <= 1000100000)))) ,
  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |-> ((Znth 0 inc_values_2 0) - (Znth 0 values 0) ))
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((Zlength (dec_values_2)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values_2 ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = 1) ” 
  &&  “ (PartialPrefixCosts values inc_values_2 pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 1)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000))) ”
  &&  (Int64Array.seg pre_pre 0 1 pre_values )
).

Definition solver_entail_wit_8 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = i)) (PreH13 : (PartialPrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values_2 0)) /\ ((Znth k_3 pre_values_2 0) <= 100010000000000)))) ,
  (Int64Array.seg pre_pre 0 (i + 1 ) (app (pre_values_2) ((cons (((Znth ((i - 1 ) - 0 ) pre_values_2 0) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = (i + 1 )) ” 
  &&  “ (PartialPrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg pre_pre 0 (i + 1 ) pre_values )
  **  (Int64Array.undef_seg pre_pre (i + 1 ) n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = i)) (PreH13 : (PartialPrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values_2 0)) /\ ((Znth k_3 pre_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ (PartialPrefixCosts values inc_values_2 (app (pre_values_2) ((cons (((Znth ((i - 1 ) - 0 ) pre_values_2 0) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (pre_values_2) ((cons (((Znth ((i - 1 ) - 0 ) pre_values_2 0) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = i)) (PreH13 : (PartialPrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values_2 0)) /\ ((Znth k_3 pre_values_2 0) <= 100010000000000)))) ,
  (PartialPrefixCosts values inc_values_2 (app (pre_values_2) ((cons (((Znth ((i - 1 ) - 0 ) pre_values_2 0) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ((@nil Z))))) )
.

Definition solver_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = i)) (PreH13 : (PartialPrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values_2 0)) /\ ((Znth k_3 pre_values_2 0) <= 100010000000000)))) ,
  ((Zlength ((app (pre_values_2) ((cons (((Znth ((i - 1 ) - 0 ) pre_values_2 0) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_9 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = i)) (PreH13 : (PartialPrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)))) (PreH15 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < i)) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.seg pre_pre 0 i pre_values_2 )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  EX (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
) \/
(
forall (pre_pre: Z) (n_pre: Z) (values: (@list Z)) (pre_values_2: (@list Z)) (i: Z) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values_2)) = i)) (PreH13 : (PartialPrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)))) (PreH15 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < i)) -> ((0 <= (Znth k_5 pre_values_2 0)) /\ ((Znth k_5 pre_values_2 0) <= 100010000000000)))) ,
  (Int64Array.seg pre_pre 0 i pre_values_2 )
|--
  EX (pre_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((Zlength (dec_values_2)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values_2 ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values_2 pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full pre_pre n_pre pre_values )
).

Definition solver_entail_wit_10 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (pre_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : ((Zlength (dec_values_2)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values_2 )) (PreH9 : ((Zlength (pre_values_2)) = n_pre)) (PreH10 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((((((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_5 dec_values_2 0))) /\ ((Znth k_5 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_5 pre_values_2 0))) /\ ((Znth k_5 pre_values_2 0) <= 100010000000000)))) ,
  (Int64Array.undef_seg suf_pre 0 (n_pre - 1 ) )
  **  (((suf_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> ((Znth (n_pre - 1 ) dec_values_2 0) - (Znth (n_pre - 1 ) values 0) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - (n_pre - 2 ) ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 ((n_pre - 2 ) + 1 ) )
  **  (Int64Array.seg suf_pre ((n_pre - 2 ) + 1 ) n_pre suf_values )
) \/
(
forall (suf_pre: Z) (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (pre_values_2: (@list Z)) (PreH1 : (((Znth (n_pre - 1 ) dec_values_2 0) - (Znth (n_pre - 1 ) values 0) ) <= INT64_MAX)) (PreH2 : (((Znth (n_pre - 1 ) dec_values_2 0) - (Znth (n_pre - 1 ) values 0) ) >= INT64_MIN)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 values 0)) /\ ((Znth k_4 values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values_2)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values_2 )) (PreH9 : ((Zlength (dec_values_2)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values_2 )) (PreH11 : ((Zlength (pre_values_2)) = n_pre)) (PreH12 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH13 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((((((1 <= (Znth k_5 inc_values_2 0)) /\ ((Znth k_5 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_5 dec_values_2 0))) /\ ((Znth k_5 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_5 pre_values_2 0))) /\ ((Znth k_5 pre_values_2 0) <= 100010000000000)))) ,
  (((suf_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> ((Znth (n_pre - 1 ) dec_values_2 0) - (Znth (n_pre - 1 ) values 0) ))
|--
  EX (suf_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((Zlength (dec_values_2)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values_2 ) ” 
  &&  “ ((Zlength (pre_values_2)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values_2 pre_values_2 ) ” 
  &&  “ ((-1) <= (n_pre - 2 )) ” 
  &&  “ ((n_pre - 2 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - (n_pre - 2 ) ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values_2 suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.seg suf_pre ((n_pre - 2 ) + 1 ) n_pre suf_values )
).

Definition solver_entail_wit_11 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values_2: (@list Z)) (i: Z) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : ((Zlength (pre_values_2)) = n_pre)) (PreH11 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values_2)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values_2)))) -> ((0 <= (Znth k_3 suf_values_2 0)) /\ ((Znth k_3 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.undef_seg suf_pre 0 i )
  **  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> ((Znth ((i + 1 ) - (i + 1 ) ) suf_values_2 0) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ))
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - (i - 1 ) ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 ((i - 1 ) + 1 ) )
  **  (Int64Array.seg suf_pre ((i - 1 ) + 1 ) n_pre suf_values )
) \/
(
forall (suf_pre: Z) (n_pre: Z) (values: (@list Z)) (suf_values_2: (@list Z)) (i: Z) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (((Znth ((i + 1 ) - (i + 1 ) ) suf_values_2 0) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) <= INT64_MAX)) (PreH2 : (((Znth ((i + 1 ) - (i + 1 ) ) suf_values_2 0) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) >= INT64_MIN)) (PreH3 : (i >= 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((-1) <= i)) (PreH15 : (i <= (n_pre - 2 ))) (PreH16 : ((Zlength (suf_values_2)) = ((n_pre - i ) - 1 ))) (PreH17 : (PartialSuffixCosts values dec_values_2 suf_values_2 )) (PreH18 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)))) (PreH19 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values_2)))) -> ((0 <= (Znth k_3 suf_values_2 0)) /\ ((Znth k_3 suf_values_2 0) <= 100010000000000)))) ,
  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> ((Znth ((i + 1 ) - (i + 1 ) ) suf_values_2 0) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ))
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values_2 )
|--
  EX (suf_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((Zlength (dec_values_2)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values_2 ) ” 
  &&  “ ((Zlength (pre_values_2)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values_2 pre_values_2 ) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - (i - 1 ) ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values_2 suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.seg suf_pre ((i - 1 ) + 1 ) n_pre suf_values )
).

Definition solver_entail_wit_12 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values_2: (@list Z)) (i: Z) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : ((Zlength (pre_values_2)) = n_pre)) (PreH11 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values_2)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_4 pre_values_2 0))) /\ ((Znth k_4 pre_values_2 0) <= 100010000000000)))) (PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength (suf_values_2)))) -> ((0 <= (Znth k_5 suf_values_2 0)) /\ ((Znth k_5 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (suf_pre: Z) (n_pre: Z) (values: (@list Z)) (suf_values_2: (@list Z)) (i: Z) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (i < 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values_2)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values_2 )) (PreH8 : ((Zlength (dec_values_2)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values_2 )) (PreH10 : ((Zlength (pre_values_2)) = n_pre)) (PreH11 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values_2)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_4 pre_values_2 0))) /\ ((Znth k_4 pre_values_2 0) <= 100010000000000)))) (PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < (Zlength (suf_values_2)))) -> ((0 <= (Znth k_5 suf_values_2 0)) /\ ((Znth k_5 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values_2 )
|--
  EX (suf_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values_2)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values_2 ) ” 
  &&  “ ((Zlength (dec_values_2)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values_2 ) ” 
  &&  “ ((Zlength (pre_values_2)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values_2 pre_values_2 ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values_2 suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full suf_pre n_pre suf_values )
).

Definition solver_entail_wit_13 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (pre_values_2: (@list Z)) (suf_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : ((Zlength (dec_values_2)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values_2 )) (PreH9 : ((Zlength (pre_values_2)) = n_pre)) (PreH10 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH11 : ((Zlength (suf_values_2)) = n_pre)) (PreH12 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_4 pre_values_2 0))) /\ ((Znth k_4 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_4 suf_values_2 0))) /\ ((Znth k_4 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
  **  (Int64Array.full suf_pre n_pre suf_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values 0 (-1) ) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (pre_values_2: (@list Z)) (suf_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : ((Zlength (dec_values_2)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values_2 )) (PreH9 : ((Zlength (pre_values_2)) = n_pre)) (PreH10 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH11 : ((Zlength (suf_values_2)) = n_pre)) (PreH12 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_4 pre_values_2 0))) /\ ((Znth k_4 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_4 suf_values_2 0))) /\ ((Znth k_4 suf_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000))) ” 
  &&  “ (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 0 (-1) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ”
  &&  emp
).

Definition solver_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (pre_values_2: (@list Z)) (suf_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : ((Zlength (dec_values_2)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values_2 )) (PreH9 : ((Zlength (pre_values_2)) = n_pre)) (PreH10 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH11 : ((Zlength (suf_values_2)) = n_pre)) (PreH12 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_4 pre_values_2 0))) /\ ((Znth k_4 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_4 suf_values_2 0))) /\ ((Znth k_4 suf_values_2 0) <= 100010000000000)))) ,
  forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))
.

Definition solver_entail_wit_13_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (pre_values_2: (@list Z)) (suf_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : ((Zlength (dec_values_2)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values_2 )) (PreH9 : ((Zlength (pre_values_2)) = n_pre)) (PreH10 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH11 : ((Zlength (suf_values_2)) = n_pre)) (PreH12 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_4 pre_values_2 0))) /\ ((Znth k_4 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_4 suf_values_2 0))) /\ ((Znth k_4 suf_values_2 0) <= 100010000000000)))) ,
  (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 0 (-1) )
.

Definition solver_entail_wit_13_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (inc_values_2: (@list Z)) (dec_values_2: (@list Z)) (pre_values_2: (@list Z)) (suf_values_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 values 0)) /\ ((Znth k_3 values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values_2)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values_2 )) (PreH7 : ((Zlength (dec_values_2)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values_2 )) (PreH9 : ((Zlength (pre_values_2)) = n_pre)) (PreH10 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH11 : ((Zlength (suf_values_2)) = n_pre)) (PreH12 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((((((((1 <= (Znth k_4 inc_values_2 0)) /\ ((Znth k_4 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_4 dec_values_2 0))) /\ ((Znth k_4 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_4 pre_values_2 0))) /\ ((Znth k_4 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_4 suf_values_2 0))) /\ ((Znth k_4 suf_values_2 0) <= 100010000000000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))
.

Definition solver_entail_wit_14_1 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full suf_pre n_pre suf_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) ) ” 
  &&  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) <= 200020000000000) ” 
  &&  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_14_1_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) <= 200020000000000)
.

Definition solver_entail_wit_14_1_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ))
.

Definition solver_entail_wit_14_1_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) )
.

Definition solver_entail_wit_14_2 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full suf_pre n_pre suf_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) ) ” 
  &&  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) <= 200020000000000) ” 
  &&  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_14_2_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) <= 200020000000000)
.

Definition solver_entail_wit_14_2_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ))
.

Definition solver_entail_wit_14_2_split_goal_3 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : (best < 0)) (PreH2 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH3 : (i < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (n_pre = (Zlength (values)))) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH8 : ((Zlength (inc_values_2)) = n_pre)) (PreH9 : (LeftProfilePrefix values inc_values_2 )) (PreH10 : ((Zlength (dec_values_2)) = n_pre)) (PreH11 : (RightProfileSuffix values dec_values_2 )) (PreH12 : ((Zlength (pre_values_2)) = n_pre)) (PreH13 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH14 : ((Zlength (suf_values_2)) = n_pre)) (PreH15 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH16 : (0 <= i)) (PreH17 : (i <= n_pre)) (PreH18 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH19 : ((-1) <= best)) (PreH20 : (best <= 200020000000000)) (PreH21 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) )
.

Definition solver_entail_wit_14_3 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full suf_pre n_pre suf_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) ) ” 
  &&  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_14_3_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ))
.

Definition solver_entail_wit_14_3_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) )
.

Definition solver_entail_wit_14_4 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full suf_pre n_pre suf_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) ) ” 
  &&  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) )) ” 
  &&  “ (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_14_4_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  ((-1) <= (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ))
.

Definition solver_entail_wit_14_4_split_goal_2 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) < best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) (((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) )
.

Definition solver_entail_wit_14_5 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full suf_pre n_pre suf_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values (i + 1 ) best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_14_5_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i inc_values_2 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) > (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) best )
.

Definition solver_entail_wit_14_6 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values_2 )
  **  (Int64Array.full inc_pre n_pre inc_values_2 )
  **  (Int64Array.full suf_pre n_pre suf_values_2 )
  **  (Int64Array.full pre_pre n_pre pre_values_2 )
|--
  EX (suf_values: (@list Z))  (pre_values: (@list Z))  (dec_values: (@list Z))  (inc_values: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values (i + 1 ) best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
) \/
(
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  TT && emp 
|--
  “ (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_14_6_split_goal_1 := 
forall (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values_2: (@list Z)) (pre_values_2: (@list Z)) (dec_values_2: (@list Z)) (inc_values_2: (@list Z)) (PreH1 : ((((((Znth i pre_values_2 0) + (Znth i suf_values_2 0) ) - ((Znth i inc_values_2 0) - (Znth i values 0) ) ) - ((Znth i dec_values_2 0) - (Znth i values 0) ) ) + ((Znth i dec_values_2 0) - (Znth i values 0) ) ) >= best)) (PreH2 : (best >= 0)) (PreH3 : ((Znth i inc_values_2 0) <= (Znth i dec_values_2 0))) (PreH4 : (i < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100000)) (PreH7 : (n_pre = (Zlength (values)))) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH9 : ((Zlength (inc_values_2)) = n_pre)) (PreH10 : (LeftProfilePrefix values inc_values_2 )) (PreH11 : ((Zlength (dec_values_2)) = n_pre)) (PreH12 : (RightProfileSuffix values dec_values_2 )) (PreH13 : ((Zlength (pre_values_2)) = n_pre)) (PreH14 : (PrefixCosts values inc_values_2 pre_values_2 )) (PreH15 : ((Zlength (suf_values_2)) = n_pre)) (PreH16 : (SuffixCosts values dec_values_2 suf_values_2 )) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 i best )) (PreH20 : ((-1) <= best)) (PreH21 : (best <= 200020000000000)) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values_2 0)) /\ ((Znth k_2 inc_values_2 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values_2 0))) /\ ((Znth k_2 dec_values_2 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values_2 0))) /\ ((Znth k_2 pre_values_2 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values_2 0))) /\ ((Znth k_2 suf_values_2 0) <= 100010000000000)))) ,
  (BestPeakPrefix values inc_values_2 dec_values_2 pre_values_2 suf_values_2 (i + 1 ) best )
.

Definition solver_return_wit_1 := 
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((Zlength (suf_values)) = n_pre)) (PreH13 : (SuffixCosts values dec_values suf_values )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH17 : ((-1) <= best)) (PreH18 : (best <= 200020000000000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (Spec values best ) ”
  &&  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full_shape inc_pre n_pre )
  **  (Int64Array.full_shape dec_pre n_pre )
  **  (Int64Array.full_shape pre_pre n_pre )
  **  (Int64Array.full_shape suf_pre n_pre )
) \/
(
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((Zlength (suf_values)) = n_pre)) (PreH13 : (SuffixCosts values dec_values suf_values )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH17 : ((-1) <= best)) (PreH18 : (best <= 200020000000000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (Spec values best ) ”
  &&  (Int64Array.full_shape inc_pre n_pre )
  **  (Int64Array.full_shape dec_pre n_pre )
  **  (Int64Array.full_shape pre_pre n_pre )
  **  (Int64Array.full_shape suf_pre n_pre )
).

Definition solver_return_wit_1_split_goal_1 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((Zlength (suf_values)) = n_pre)) (PreH13 : (SuffixCosts values dec_values suf_values )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH17 : ((-1) <= best)) (PreH18 : (best <= 200020000000000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (Spec values best ) ”
.

Definition solver_return_wit_1_split_goal_spatial := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((Zlength (suf_values)) = n_pre)) (PreH13 : (SuffixCosts values dec_values suf_values )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH17 : ((-1) <= best)) (PreH18 : (best <= 200020000000000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  (Int64Array.full_shape inc_pre n_pre )
  **  (Int64Array.full_shape dec_pre n_pre )
  **  (Int64Array.full_shape pre_pre n_pre )
  **  (Int64Array.full_shape suf_pre n_pre )
.

Definition solver_partial_solve_wit_1 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full inc_pre n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (((a_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 values 0))
  **  (Int64Array.missing_i a_pre 0 0 n_pre values )
  **  (Int64Array.undef_full inc_pre n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_2 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000)))) (PreH4 : (n_pre = (Zlength (values)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full inc_pre n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((1 <= (Znth i values 0)) /\ ((Znth i values 0) <= 1000000000))) ” 
  &&  “ (n_pre = (Zlength (values))) ”
  &&  (((inc_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg inc_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_3 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values)) = i)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = i) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_4 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (inc_values)) = i)) (PreH9 : (LeftProfilePrefix values inc_values )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = i) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((inc_pre + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - 1 ) - 0 ) inc_values 0))
  **  (Int64Array.missing_i inc_pre (i - 1 ) 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_5 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = i) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_6 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = i) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((inc_pre + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - 1 ) - 0 ) inc_values 0))
  **  (Int64Array.missing_i inc_pre (i - 1 ) 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_7 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) > ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = i) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((inc_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_8 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (i: Z) (PreH1 : ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 ))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (inc_values)) = i)) (PreH10 : (LeftProfilePrefix values inc_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_seg inc_pre i n_pre )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) <= ((Znth ((i - 1 ) - 0 ) inc_values 0) + 1 )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (inc_values)) = i) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((inc_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg inc_pre (i + 1 ) n_pre )
  **  (Int64Array.seg inc_pre 0 i inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_9 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((a_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - 1 ) values 0))
  **  (Int64Array.missing_i a_pre (n_pre - 1 ) 0 n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_10 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full dec_pre n_pre )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ”
  &&  (((dec_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i dec_pre (n_pre - 1 ) 0 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_11 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_12 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((-1) <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH11 : (RightProfileSuffix values dec_values )) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH13 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((dec_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i + 1 ) - (i + 1 ) ) dec_values 0))
  **  (Int64Array.missing_i dec_pre (i + 1 ) (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_13 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) > ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) > ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_14 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((dec_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i + 1 ) - (i + 1 ) ) dec_values 0))
  **  (Int64Array.missing_i dec_pre (i + 1 ) (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_15 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) > ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) > ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((dec_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i dec_pre i 0 (i + 1 ) )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_16 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (dec_values: (@list Z)) (i: Z) (inc_values: (@list Z)) (PreH1 : ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 ))) (PreH2 : (i >= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((-1) <= i)) (PreH10 : (i <= (n_pre - 2 ))) (PreH11 : ((Zlength (dec_values)) = ((n_pre - i ) - 1 ))) (PreH12 : (RightProfileSuffix values dec_values )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH14 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_seg dec_pre 0 (i + 1 ) )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ ((Znth i values 0) <= ((Znth ((i + 1 ) - (i + 1 ) ) dec_values 0) + 1 )) ” 
  &&  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (dec_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (dec_values)))) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((dec_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i dec_pre i 0 (i + 1 ) )
  **  (Int64Array.seg dec_pre (i + 1 ) n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_17 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((inc_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 inc_values 0))
  **  (Int64Array.missing_i inc_pre 0 0 n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_18 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((a_pre + (0 * sizeof(INT64)))) # Int64  |-> (Znth 0 values 0))
  **  (Int64Array.missing_i a_pre 0 0 n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_19 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)))) (PreH10 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full pre_pre n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 dec_values 0)) /\ ((Znth k_3 dec_values 0) <= 1000100000))) ”
  &&  (((pre_pre + (0 * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg pre_pre 1 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_20 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = i) ” 
  &&  “ (PartialPrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000))) ”
  &&  (((pre_pre + ((i - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i - 1 ) - 0 ) pre_values 0))
  **  (Int64Array.missing_i pre_pre (i - 1 ) 0 i pre_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_21 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = i) ” 
  &&  “ (PartialPrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000))) ”
  &&  (((inc_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i inc_values 0))
  **  (Int64Array.missing_i inc_pre i 0 n_pre inc_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_22 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = i) ” 
  &&  “ (PartialPrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_23 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (pre_values: (@list Z)) (i: Z) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : ((Zlength (pre_values)) = i)) (PreH13 : (PartialPrefixCosts values inc_values pre_values )) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_seg pre_pre i n_pre )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (pre_values)) = i) ” 
  &&  “ (PartialPrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((0 <= (Znth k_3 pre_values 0)) /\ ((Znth k_3 pre_values 0) <= 100010000000000))) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg pre_pre (i + 1 ) n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.seg pre_pre 0 i pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_24 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ”
  &&  (((dec_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - 1 ) dec_values 0))
  **  (Int64Array.missing_i dec_pre (n_pre - 1 ) 0 n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_25 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ”
  &&  (((a_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (n_pre - 1 ) values 0))
  **  (Int64Array.missing_i a_pre (n_pre - 1 ) 0 n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
.

Definition solver_partial_solve_wit_26 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (inc_values: (@list Z)) (dec_values: (@list Z)) (pre_values: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (n_pre = (Zlength (values)))) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH5 : ((Zlength (inc_values)) = n_pre)) (PreH6 : (LeftProfilePrefix values inc_values )) (PreH7 : ((Zlength (dec_values)) = n_pre)) (PreH8 : (RightProfileSuffix values dec_values )) (PreH9 : ((Zlength (pre_values)) = n_pre)) (PreH10 : (PrefixCosts values inc_values pre_values )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_full suf_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ”
  &&  (((suf_pre + ((n_pre - 1 ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i suf_pre (n_pre - 1 ) 0 n_pre )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Definition solver_partial_solve_wit_27 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
|--
  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (((suf_pre + ((i + 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((i + 1 ) - (i + 1 ) ) suf_values 0))
  **  (Int64Array.missing_i suf_pre (i + 1 ) (i + 1 ) n_pre suf_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
.

Definition solver_partial_solve_wit_28 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
|--
  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i dec_values 0))
  **  (Int64Array.missing_i dec_pre i 0 n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
.

Definition solver_partial_solve_wit_29 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
|--
  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
.

Definition solver_partial_solve_wit_30 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (suf_values: (@list Z)) (i: Z) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i >= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((-1) <= i)) (PreH13 : (i <= (n_pre - 2 ))) (PreH14 : ((Zlength (suf_values)) = ((n_pre - i ) - 1 ))) (PreH15 : (PartialSuffixCosts values dec_values suf_values )) (PreH16 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)))) (PreH17 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.undef_seg suf_pre 0 (i + 1 ) )
|--
  “ (i >= 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ ((Zlength (suf_values)) = ((n_pre - i ) - 1 )) ” 
  &&  “ (PartialSuffixCosts values dec_values suf_values ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (Zlength (suf_values)))) -> ((0 <= (Znth k_3 suf_values 0)) /\ ((Znth k_3 suf_values 0) <= 100010000000000))) ”
  &&  (((suf_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_missing_i suf_pre i 0 (i + 1 ) )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.seg suf_pre (i + 1 ) n_pre suf_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Definition solver_partial_solve_wit_31 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((Zlength (suf_values)) = n_pre)) (PreH13 : (SuffixCosts values dec_values suf_values )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH17 : ((-1) <= best)) (PreH18 : (best <= 200020000000000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((inc_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i inc_values 0))
  **  (Int64Array.missing_i inc_pre i 0 n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
.

Definition solver_partial_solve_wit_32 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (n_pre = (Zlength (values)))) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH6 : ((Zlength (inc_values)) = n_pre)) (PreH7 : (LeftProfilePrefix values inc_values )) (PreH8 : ((Zlength (dec_values)) = n_pre)) (PreH9 : (RightProfileSuffix values dec_values )) (PreH10 : ((Zlength (pre_values)) = n_pre)) (PreH11 : (PrefixCosts values inc_values pre_values )) (PreH12 : ((Zlength (suf_values)) = n_pre)) (PreH13 : (SuffixCosts values dec_values suf_values )) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH17 : ((-1) <= best)) (PreH18 : (best <= 200020000000000)) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i dec_values 0))
  **  (Int64Array.missing_i dec_pre i 0 n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
.

Definition solver_partial_solve_wit_33 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((inc_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i inc_values 0))
  **  (Int64Array.missing_i inc_pre i 0 n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
.

Definition solver_partial_solve_wit_34 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i dec_values 0))
  **  (Int64Array.missing_i dec_pre i 0 n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
.

Definition solver_partial_solve_wit_35 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i pre_values 0))
  **  (Int64Array.missing_i pre_pre i 0 n_pre pre_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full suf_pre n_pre suf_values )
.

Definition solver_partial_solve_wit_36 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i suf_values 0))
  **  (Int64Array.missing_i suf_pre i 0 n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_37 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((inc_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i inc_values 0))
  **  (Int64Array.missing_i inc_pre i 0 n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_38 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
.

Definition solver_partial_solve_wit_39 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i dec_values 0))
  **  (Int64Array.missing_i dec_pre i 0 n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Definition solver_partial_solve_wit_40 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Definition solver_partial_solve_wit_41 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) > (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
|--
  “ ((Znth i inc_values 0) > (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Definition solver_partial_solve_wit_42 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((pre_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i pre_values 0))
  **  (Int64Array.missing_i pre_pre i 0 n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full suf_pre n_pre suf_values )
.

Definition solver_partial_solve_wit_43 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full suf_pre n_pre suf_values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((suf_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i suf_values 0))
  **  (Int64Array.missing_i suf_pre i 0 n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_44 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((inc_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i inc_values 0))
  **  (Int64Array.missing_i inc_pre i 0 n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
.

Definition solver_partial_solve_wit_45 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
.

Definition solver_partial_solve_wit_46 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
  **  (Int64Array.full dec_pre n_pre dec_values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((dec_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i dec_values 0))
  **  (Int64Array.missing_i dec_pre i 0 n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Definition solver_partial_solve_wit_47 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Definition solver_partial_solve_wit_48 := 
forall (suf_pre: Z) (pre_pre: Z) (dec_pre: Z) (inc_pre: Z) (n_pre: Z) (a_pre: Z) (values: (@list Z)) (best: Z) (i: Z) (suf_values: (@list Z)) (pre_values: (@list Z)) (dec_values: (@list Z)) (inc_values: (@list Z)) (PreH1 : ((Znth i inc_values 0) <= (Znth i dec_values 0))) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (n_pre = (Zlength (values)))) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000)))) (PreH7 : ((Zlength (inc_values)) = n_pre)) (PreH8 : (LeftProfilePrefix values inc_values )) (PreH9 : ((Zlength (dec_values)) = n_pre)) (PreH10 : (RightProfileSuffix values dec_values )) (PreH11 : ((Zlength (pre_values)) = n_pre)) (PreH12 : (PrefixCosts values inc_values pre_values )) (PreH13 : ((Zlength (suf_values)) = n_pre)) (PreH14 : (SuffixCosts values dec_values suf_values )) (PreH15 : (0 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (BestPeakPrefix values inc_values dec_values pre_values suf_values i best )) (PreH18 : ((-1) <= best)) (PreH19 : (best <= 200020000000000)) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000)))) ,
  (Int64Array.full a_pre n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
|--
  “ ((Znth i inc_values 0) <= (Znth i dec_values 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (n_pre = (Zlength (values))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k values 0)) /\ ((Znth k values 0) <= 1000000000))) ” 
  &&  “ ((Zlength (inc_values)) = n_pre) ” 
  &&  “ (LeftProfilePrefix values inc_values ) ” 
  &&  “ ((Zlength (dec_values)) = n_pre) ” 
  &&  “ (RightProfileSuffix values dec_values ) ” 
  &&  “ ((Zlength (pre_values)) = n_pre) ” 
  &&  “ (PrefixCosts values inc_values pre_values ) ” 
  &&  “ ((Zlength (suf_values)) = n_pre) ” 
  &&  “ (SuffixCosts values dec_values suf_values ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (BestPeakPrefix values inc_values dec_values pre_values suf_values i best ) ” 
  &&  “ ((-1) <= best) ” 
  &&  “ (best <= 200020000000000) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((((((((1 <= (Znth k_2 inc_values 0)) /\ ((Znth k_2 inc_values 0) <= 1000100000)) /\ (1 <= (Znth k_2 dec_values 0))) /\ ((Znth k_2 dec_values 0) <= 1000100000)) /\ (0 <= (Znth k_2 pre_values 0))) /\ ((Znth k_2 pre_values 0) <= 100010000000000)) /\ (0 <= (Znth k_2 suf_values 0))) /\ ((Znth k_2 suf_values 0) <= 100010000000000))) ”
  &&  (((a_pre + (i * sizeof(INT64)))) # Int64  |-> (Znth i values 0))
  **  (Int64Array.missing_i a_pre i 0 n_pre values )
  **  (Int64Array.full dec_pre n_pre dec_values )
  **  (Int64Array.full inc_pre n_pre inc_values )
  **  (Int64Array.full suf_pre n_pre suf_values )
  **  (Int64Array.full pre_pre n_pre pre_values )
.

Module Type VC_Correct.


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
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_safety_wit_57 : solver_safety_wit_57.
Axiom proof_of_solver_safety_wit_58 : solver_safety_wit_58.
Axiom proof_of_solver_safety_wit_59 : solver_safety_wit_59.
Axiom proof_of_solver_safety_wit_60 : solver_safety_wit_60.
Axiom proof_of_solver_safety_wit_61 : solver_safety_wit_61.
Axiom proof_of_solver_safety_wit_62 : solver_safety_wit_62.
Axiom proof_of_solver_safety_wit_63 : solver_safety_wit_63.
Axiom proof_of_solver_safety_wit_64 : solver_safety_wit_64.
Axiom proof_of_solver_safety_wit_65 : solver_safety_wit_65.
Axiom proof_of_solver_safety_wit_66 : solver_safety_wit_66.
Axiom proof_of_solver_safety_wit_67 : solver_safety_wit_67.
Axiom proof_of_solver_safety_wit_68 : solver_safety_wit_68.
Axiom proof_of_solver_safety_wit_69 : solver_safety_wit_69.
Axiom proof_of_solver_safety_wit_70 : solver_safety_wit_70.
Axiom proof_of_solver_safety_wit_71 : solver_safety_wit_71.
Axiom proof_of_solver_safety_wit_72 : solver_safety_wit_72.
Axiom proof_of_solver_safety_wit_73 : solver_safety_wit_73.
Axiom proof_of_solver_safety_wit_74 : solver_safety_wit_74.
Axiom proof_of_solver_safety_wit_75 : solver_safety_wit_75.
Axiom proof_of_solver_safety_wit_76 : solver_safety_wit_76.
Axiom proof_of_solver_safety_wit_77 : solver_safety_wit_77.
Axiom proof_of_solver_safety_wit_78 : solver_safety_wit_78.
Axiom proof_of_solver_safety_wit_79 : solver_safety_wit_79.
Axiom proof_of_solver_safety_wit_80 : solver_safety_wit_80.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3.
Axiom proof_of_solver_entail_wit_14_4 : solver_entail_wit_14_4.
Axiom proof_of_solver_entail_wit_14_5 : solver_entail_wit_14_5.
Axiom proof_of_solver_entail_wit_14_6 : solver_entail_wit_14_6.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.
Axiom proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29.
Axiom proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30.
Axiom proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31.
Axiom proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32.
Axiom proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33.
Axiom proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34.
Axiom proof_of_solver_partial_solve_wit_35 : solver_partial_solve_wit_35.
Axiom proof_of_solver_partial_solve_wit_36 : solver_partial_solve_wit_36.
Axiom proof_of_solver_partial_solve_wit_37 : solver_partial_solve_wit_37.
Axiom proof_of_solver_partial_solve_wit_38 : solver_partial_solve_wit_38.
Axiom proof_of_solver_partial_solve_wit_39 : solver_partial_solve_wit_39.
Axiom proof_of_solver_partial_solve_wit_40 : solver_partial_solve_wit_40.
Axiom proof_of_solver_partial_solve_wit_41 : solver_partial_solve_wit_41.
Axiom proof_of_solver_partial_solve_wit_42 : solver_partial_solve_wit_42.
Axiom proof_of_solver_partial_solve_wit_43 : solver_partial_solve_wit_43.
Axiom proof_of_solver_partial_solve_wit_44 : solver_partial_solve_wit_44.
Axiom proof_of_solver_partial_solve_wit_45 : solver_partial_solve_wit_45.
Axiom proof_of_solver_partial_solve_wit_46 : solver_partial_solve_wit_46.
Axiom proof_of_solver_partial_solve_wit_47 : solver_partial_solve_wit_47.
Axiom proof_of_solver_partial_solve_wit_48 : solver_partial_solve_wit_48.

End VC_Correct.
