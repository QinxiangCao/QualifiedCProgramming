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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P060_1930D1_sum_over_all_substrings_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH4 : (n_pre = (Zlength (bits)))) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH4 : (n_pre = (Zlength (bits)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int64  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  ((( &( "cover" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  ((( &( "cover" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  ((( &( "cnt" ) )) # Int64  |->_)
  **  ((( &( "cover" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k > cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((cnt + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (cnt + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k > cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "cnt" ) )) # Int64  |-> (cnt + 1 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((k + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 2 )) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k > cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "cnt" ) )) # Int64  |-> (cnt + 1 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) (cnt + 1 ) )) (PreH2 : (k > cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base)) (PreH18 : (base <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total)) (PreH20 : (row_total <= ((k - i ) * n_pre ))) (PreH21 : (total = (base + row_total ))) (PreH22 : (CompletedRows bits i base )) (PreH23 : (CurrentRow bits i k row_total )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((( &( "cnt" ) )) # Int64  |-> (cnt + 1 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cover" ) )) # Int  |-> (k + 2 ))
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + (cnt + 1 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + (cnt + 1 ) )) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : ((Znth k bits 0) <> 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + cnt ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + cnt )) ”
.

Definition solver_safety_wit_12 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : (k <= cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base)) (PreH18 : (base <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total)) (PreH20 : (row_total <= ((k - i ) * n_pre ))) (PreH21 : (total = (base + row_total ))) (PreH22 : (CompletedRows bits i base )) (PreH23 : (CurrentRow bits i k row_total )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "total" ) )) # Int64  |-> total)
|--
  “ ((total + cnt ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (total + cnt )) ”
.

Definition solver_safety_wit_13 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) (cnt + 1 ) )) (PreH2 : (k > cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base)) (PreH18 : (base <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total)) (PreH20 : (row_total <= ((k - i ) * n_pre ))) (PreH21 : (total = (base + row_total ))) (PreH22 : (CompletedRows bits i base )) (PreH23 : (CurrentRow bits i k row_total )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((( &( "cnt" ) )) # Int64  |-> (cnt + 1 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cover" ) )) # Int  |-> (k + 2 ))
  **  ((( &( "total" ) )) # Int64  |-> (total + (cnt + 1 ) ))
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_14 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : ((Znth k bits 0) <> 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "total" ) )) # Int64  |-> (total + cnt ))
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : (k <= cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base)) (PreH18 : (base <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total)) (PreH20 : (row_total <= ((k - i ) * n_pre ))) (PreH21 : (total = (base + row_total ))) (PreH22 : (CompletedRows bits i base )) (PreH23 : (CurrentRow bits i k row_total )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "total" ) )) # Int64  |-> (total + cnt ))
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition solver_safety_wit_16 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int64  |-> total)
  **  (CharArray.full s_pre n_pre bits )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH4 : (n_pre = (Zlength (bits)))) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((0 * n_pre ) * n_pre )) ” 
  &&  “ (CompletedRows bits 0 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH4 : (n_pre = (Zlength (bits)))) ,
  TT && emp 
|--
  “ (CompletedRows bits 0 0 ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH4 : (n_pre = (Zlength (bits)))) ,
  (CompletedRows bits 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (bits: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> (((Znth i bits 0) = 48) \/ ((Znth i bits 0) = 49)))) (PreH4 : (n_pre = (Zlength (bits)))) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))
.

Definition solver_entail_wit_2 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 bits 0) = 48) \/ ((Znth j_2 bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  (CharArray.full s_pre n_pre bits )
|--
  EX (row_total: Z)  (base: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((i - 1 ) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= ((i - i ) * n_pre )) ” 
  &&  “ (total = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i i row_total ) ” 
  &&  “ (PrefixCoverSummary bits i i (i - 1 ) 0 ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 bits 0) = 48) \/ ((Znth j_2 bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  TT && emp 
|--
  EX (row_total: Z)  (base: Z) ,
  “ (i <= i) ” 
  &&  “ ((i - 1 ) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * (Zlength (bits)) ) * (Zlength (bits)) )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= ((i - i ) * (Zlength (bits)) )) ” 
  &&  “ (total = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i i row_total ) ” 
  &&  “ (PrefixCoverSummary bits i i (i - 1 ) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_3_1 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k > cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (FValue (sublist (i) ((k + 1 )) (bits)) (cnt + 1 ) ) ” 
  &&  “ (k > cover) ” 
  &&  “ ((Znth k bits 0) = 49) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i - 1 ) <= cover) ” 
  &&  “ (cover <= (k + 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= (k - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= ((k - i ) * n_pre )) ” 
  &&  “ (total = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i k row_total ) ” 
  &&  “ (PrefixCoverSummary bits i k cover cnt ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k > cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  TT && emp 
|--
  “ (FValue (sublist (i) ((k + 1 )) (bits)) (cnt + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k > cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (FValue (sublist (i) ((k + 1 )) (bits)) (cnt + 1 ) )
.

Definition solver_entail_wit_3_2 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : ((Znth k bits 0) <> 49)) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (n_pre = (Zlength (bits)))) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i <= k)) (PreH10 : (k <= n_pre)) (PreH11 : ((i - 1 ) <= cover)) (PreH12 : (cover <= (k + 1 ))) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= (k - i ))) (PreH15 : (0 <= base)) (PreH16 : (base <= ((i * n_pre ) * n_pre ))) (PreH17 : (0 <= row_total)) (PreH18 : (row_total <= ((k - i ) * n_pre ))) (PreH19 : (total = (base + row_total ))) (PreH20 : (CompletedRows bits i base )) (PreH21 : (CurrentRow bits i k row_total )) (PreH22 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
|--
  “ (FValue (sublist (i) ((k + 1 )) (bits)) cnt ) ” 
  &&  “ ((Znth k bits 0) <> 49) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i - 1 ) <= cover) ” 
  &&  “ (cover <= (k + 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= (k - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= ((k - i ) * n_pre )) ” 
  &&  “ (total = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i k row_total ) ” 
  &&  “ (PrefixCoverSummary bits i k cover cnt ) ”
  &&  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "cover" ) )) # Int  |-> cover)
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : ((Znth k bits 0) <> 49)) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (n_pre = (Zlength (bits)))) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i <= k)) (PreH10 : (k <= n_pre)) (PreH11 : ((i - 1 ) <= cover)) (PreH12 : (cover <= (k + 1 ))) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= (k - i ))) (PreH15 : (0 <= base)) (PreH16 : (base <= ((i * n_pre ) * n_pre ))) (PreH17 : (0 <= row_total)) (PreH18 : (row_total <= ((k - i ) * n_pre ))) (PreH19 : (total = (base + row_total ))) (PreH20 : (CompletedRows bits i base )) (PreH21 : (CurrentRow bits i k row_total )) (PreH22 : (PrefixCoverSummary bits i k cover cnt )) ,
  TT && emp 
|--
  “ (FValue (sublist (i) ((k + 1 )) (bits)) cnt ) ”
  &&  emp
).

Definition solver_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : ((Znth k bits 0) <> 49)) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (n_pre = (Zlength (bits)))) (PreH6 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (i <= k)) (PreH10 : (k <= n_pre)) (PreH11 : ((i - 1 ) <= cover)) (PreH12 : (cover <= (k + 1 ))) (PreH13 : (0 <= cnt)) (PreH14 : (cnt <= (k - i ))) (PreH15 : (0 <= base)) (PreH16 : (base <= ((i * n_pre ) * n_pre ))) (PreH17 : (0 <= row_total)) (PreH18 : (row_total <= ((k - i ) * n_pre ))) (PreH19 : (total = (base + row_total ))) (PreH20 : (CompletedRows bits i base )) (PreH21 : (CurrentRow bits i k row_total )) (PreH22 : (PrefixCoverSummary bits i k cover cnt )) ,
  (FValue (sublist (i) ((k + 1 )) (bits)) cnt )
.

Definition solver_entail_wit_3_3 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k <= cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
  **  ((( &( "cover" ) )) # Int  |-> cover)
  **  ((( &( "cnt" ) )) # Int64  |-> cnt)
|--
  “ (FValue (sublist (i) ((k + 1 )) (bits)) cnt ) ” 
  &&  “ (k <= cover) ” 
  &&  “ ((Znth k bits 0) = 49) ” 
  &&  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i - 1 ) <= cover) ” 
  &&  “ (cover <= (k + 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= (k - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= ((k - i ) * n_pre )) ” 
  &&  “ (total = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i k row_total ) ” 
  &&  “ (PrefixCoverSummary bits i k cover cnt ) ”
  &&  ((( &( "cnt" ) )) # Int64  |-> cnt)
  **  (CharArray.full s_pre n_pre bits )
  **  ((( &( "cover" ) )) # Int  |-> cover)
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k <= cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  TT && emp 
|--
  “ (FValue (sublist (i) ((k + 1 )) (bits)) cnt ) ”
  &&  emp
).

Definition solver_entail_wit_3_3_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k <= cover)) (PreH2 : ((Znth k bits 0) = 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base)) (PreH17 : (base <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total)) (PreH19 : (row_total <= ((k - i ) * n_pre ))) (PreH20 : (total = (base + row_total ))) (PreH21 : (CompletedRows bits i base )) (PreH22 : (CurrentRow bits i k row_total )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (FValue (sublist (i) ((k + 1 )) (bits)) cnt )
.

Definition solver_entail_wit_4_1 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total_2: Z) (base_2: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) (cnt + 1 ) )) (PreH2 : (k > cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base_2)) (PreH18 : (base_2 <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total_2)) (PreH20 : (row_total_2 <= ((k - i ) * n_pre ))) (PreH21 : (total = (base_2 + row_total_2 ))) (PreH22 : (CompletedRows bits i base_2 )) (PreH23 : (CurrentRow bits i k row_total_2 )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
|--
  EX (row_total: Z)  (base: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ ((i - 1 ) <= (k + 2 )) ” 
  &&  “ ((k + 2 ) <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) <= ((k + 1 ) - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= (((k + 1 ) - i ) * n_pre )) ” 
  &&  “ ((total + (cnt + 1 ) ) = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i (k + 1 ) row_total ) ” 
  &&  “ (PrefixCoverSummary bits i (k + 1 ) (k + 2 ) (cnt + 1 ) ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total_2: Z) (base_2: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) (cnt + 1 ) )) (PreH2 : (k > cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base_2)) (PreH18 : (base_2 <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total_2)) (PreH20 : (row_total_2 <= ((k - i ) * n_pre ))) (PreH21 : (total = (base_2 + row_total_2 ))) (PreH22 : (CompletedRows bits i base_2 )) (PreH23 : (CurrentRow bits i k row_total_2 )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  TT && emp 
|--
  EX (row_total: Z)  (base: Z) ,
  “ (i <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (Zlength (bits))) ” 
  &&  “ ((i - 1 ) <= (k + 2 )) ” 
  &&  “ ((k + 2 ) <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) <= ((k + 1 ) - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * (Zlength (bits)) ) * (Zlength (bits)) )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= (((k + 1 ) - i ) * (Zlength (bits)) )) ” 
  &&  “ (((base_2 + row_total_2 ) + (cnt + 1 ) ) = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i (k + 1 ) row_total ) ” 
  &&  “ (PrefixCoverSummary bits i (k + 1 ) (k + 2 ) (cnt + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_4_2 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total_2: Z) (base_2: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : ((Znth k bits 0) <> 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base_2)) (PreH17 : (base_2 <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total_2)) (PreH19 : (row_total_2 <= ((k - i ) * n_pre ))) (PreH20 : (total = (base_2 + row_total_2 ))) (PreH21 : (CompletedRows bits i base_2 )) (PreH22 : (CurrentRow bits i k row_total_2 )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
|--
  EX (row_total: Z)  (base: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ ((i - 1 ) <= cover) ” 
  &&  “ (cover <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= ((k + 1 ) - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= (((k + 1 ) - i ) * n_pre )) ” 
  &&  “ ((total + cnt ) = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i (k + 1 ) row_total ) ” 
  &&  “ (PrefixCoverSummary bits i (k + 1 ) cover cnt ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total_2: Z) (base_2: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : ((Znth k bits 0) <> 49)) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (n_pre = (Zlength (bits)))) (PreH7 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (i <= k)) (PreH11 : (k <= n_pre)) (PreH12 : ((i - 1 ) <= cover)) (PreH13 : (cover <= (k + 1 ))) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= (k - i ))) (PreH16 : (0 <= base_2)) (PreH17 : (base_2 <= ((i * n_pre ) * n_pre ))) (PreH18 : (0 <= row_total_2)) (PreH19 : (row_total_2 <= ((k - i ) * n_pre ))) (PreH20 : (total = (base_2 + row_total_2 ))) (PreH21 : (CompletedRows bits i base_2 )) (PreH22 : (CurrentRow bits i k row_total_2 )) (PreH23 : (PrefixCoverSummary bits i k cover cnt )) ,
  TT && emp 
|--
  EX (row_total: Z)  (base: Z) ,
  “ (i <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (Zlength (bits))) ” 
  &&  “ (cover <= ((k + 1 ) + 1 )) ” 
  &&  “ (cnt <= ((k + 1 ) - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * (Zlength (bits)) ) * (Zlength (bits)) )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= (((k + 1 ) - i ) * (Zlength (bits)) )) ” 
  &&  “ (((base_2 + row_total_2 ) + cnt ) = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i (k + 1 ) row_total ) ” 
  &&  “ (PrefixCoverSummary bits i (k + 1 ) cover cnt ) ”
  &&  emp
).

Definition solver_entail_wit_4_3 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total_2: Z) (base_2: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : (k <= cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base_2)) (PreH18 : (base_2 <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total_2)) (PreH20 : (row_total_2 <= ((k - i ) * n_pre ))) (PreH21 : (total = (base_2 + row_total_2 ))) (PreH22 : (CompletedRows bits i base_2 )) (PreH23 : (CurrentRow bits i k row_total_2 )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
|--
  EX (row_total: Z)  (base: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= n_pre) ” 
  &&  “ ((i - 1 ) <= cover) ” 
  &&  “ (cover <= ((k + 1 ) + 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= ((k + 1 ) - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= (((k + 1 ) - i ) * n_pre )) ” 
  &&  “ ((total + cnt ) = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i (k + 1 ) row_total ) ” 
  &&  “ (PrefixCoverSummary bits i (k + 1 ) cover cnt ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total_2: Z) (base_2: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (FValue (sublist (i) ((k + 1 )) (bits)) cnt )) (PreH2 : (k <= cover)) (PreH3 : ((Znth k bits 0) = 49)) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 100)) (PreH7 : (n_pre = (Zlength (bits)))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (i <= k)) (PreH12 : (k <= n_pre)) (PreH13 : ((i - 1 ) <= cover)) (PreH14 : (cover <= (k + 1 ))) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= (k - i ))) (PreH17 : (0 <= base_2)) (PreH18 : (base_2 <= ((i * n_pre ) * n_pre ))) (PreH19 : (0 <= row_total_2)) (PreH20 : (row_total_2 <= ((k - i ) * n_pre ))) (PreH21 : (total = (base_2 + row_total_2 ))) (PreH22 : (CompletedRows bits i base_2 )) (PreH23 : (CurrentRow bits i k row_total_2 )) (PreH24 : (PrefixCoverSummary bits i k cover cnt )) ,
  TT && emp 
|--
  EX (row_total: Z)  (base: Z) ,
  “ (i <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (Zlength (bits))) ” 
  &&  “ (cover <= ((k + 1 ) + 1 )) ” 
  &&  “ (cnt <= ((k + 1 ) - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * (Zlength (bits)) ) * (Zlength (bits)) )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= (((k + 1 ) - i ) * (Zlength (bits)) )) ” 
  &&  “ (((base_2 + row_total_2 ) + cnt ) = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i (k + 1 ) row_total ) ” 
  &&  “ (PrefixCoverSummary bits i (k + 1 ) cover cnt ) ”
  &&  emp
).

Definition solver_entail_wit_5 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 bits 0) = 48) \/ ((Znth j_2 bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= total) ” 
  &&  “ (total <= (((i + 1 ) * n_pre ) * n_pre )) ” 
  &&  “ (CompletedRows bits (i + 1 ) total ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 bits 0) = 48) \/ ((Znth j_2 bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  TT && emp 
|--
  “ (CompletedRows bits (i + 1 ) (base + row_total ) ) ” 
  &&  “ ((base + row_total ) <= (((i + 1 ) * n_pre ) * n_pre )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 bits 0) = 48) \/ ((Znth j_2 bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CompletedRows bits (i + 1 ) (base + row_total ) )
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 bits 0) = 48) \/ ((Znth j_2 bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  ((base + row_total ) <= (((i + 1 ) * n_pre ) * n_pre ))
.

Definition solver_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> (((Znth j_2 bits 0) = 48) \/ ((Znth j_2 bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (Spec bits total ) ”
  &&  (CharArray.full s_pre n_pre bits )
) \/
(
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  TT && emp 
|--
  “ (Spec bits total ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (bits: (@list Z)) (total: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= total)) (PreH9 : (total <= ((i * n_pre ) * n_pre ))) (PreH10 : (CompletedRows bits i total )) ,
  (Spec bits total )
.

Definition solver_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (bits: (@list Z)) (total: Z) (row_total: Z) (base: Z) (cnt: Z) (cover: Z) (k: Z) (i: Z) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100)) (PreH4 : (n_pre = (Zlength (bits)))) (PreH5 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49)))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (i <= k)) (PreH9 : (k <= n_pre)) (PreH10 : ((i - 1 ) <= cover)) (PreH11 : (cover <= (k + 1 ))) (PreH12 : (0 <= cnt)) (PreH13 : (cnt <= (k - i ))) (PreH14 : (0 <= base)) (PreH15 : (base <= ((i * n_pre ) * n_pre ))) (PreH16 : (0 <= row_total)) (PreH17 : (row_total <= ((k - i ) * n_pre ))) (PreH18 : (total = (base + row_total ))) (PreH19 : (CompletedRows bits i base )) (PreH20 : (CurrentRow bits i k row_total )) (PreH21 : (PrefixCoverSummary bits i k cover cnt )) ,
  (CharArray.full s_pre n_pre bits )
|--
  “ (k < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (n_pre = (Zlength (bits))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> (((Znth j bits 0) = 48) \/ ((Znth j bits 0) = 49))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i <= k) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ ((i - 1 ) <= cover) ” 
  &&  “ (cover <= (k + 1 )) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= (k - i )) ” 
  &&  “ (0 <= base) ” 
  &&  “ (base <= ((i * n_pre ) * n_pre )) ” 
  &&  “ (0 <= row_total) ” 
  &&  “ (row_total <= ((k - i ) * n_pre )) ” 
  &&  “ (total = (base + row_total )) ” 
  &&  “ (CompletedRows bits i base ) ” 
  &&  “ (CurrentRow bits i k row_total ) ” 
  &&  “ (PrefixCoverSummary bits i k cover cnt ) ”
  &&  (((s_pre + (k * sizeof(CHAR)))) # Char  |-> (Znth k bits 0))
  **  (CharArray.missing_i s_pre k 0 n_pre bits )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.

End VC_Correct.
