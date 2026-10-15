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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P007_1313A_fast_food_restaurant_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) ,
  ((( &( "fam" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) (PreH7 : (0 <= fam)) (PreH8 : (fam <= 128)) (PreH9 : (0 <= best)) (PreH10 : (best <= 7)) (PreH11 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (128 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 128) ”
.

Definition solver_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam < 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  ((( &( "cnt" ) )) # Int  |->_)
  **  (IntArray.full ( &( "need" ) ) 3 (repeat_Z (0) (3)) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam < 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam < 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam < 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam < 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "cnt" ) )) # Int  |-> 0)
  **  (IntArray.full ( &( "need" ) ) 3 (repeat_Z (0) (3)) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_9 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) (PreH7 : (0 <= fam)) (PreH8 : (fam < 128)) (PreH9 : (0 <= best)) (PreH10 : (best <= 7)) (PreH11 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH12 : (1 <= s)) (PreH13 : (s <= 8)) (PreH14 : (0 <= cnt)) (PreH15 : (cnt <= 7)) (PreH16 : (0 <= need_a)) (PreH17 : (need_a <= 4)) (PreH18 : (0 <= need_b)) (PreH19 : (need_b <= 4)) (PreH20 : (0 <= need_c)) (PreH21 : (need_c <= 4)) (PreH22 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition solver_safety_wit_10 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((signed_last_nbits ((1 * (2^(s - 1 )) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^(s - 1 )) )) (32))) ” 
  &&  “ ((s - 1 ) <= 31) ” 
  &&  “ (0 <= (s - 1 )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((signed_last_nbits ((1 * (2^(s - 1 )) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^(s - 1 )) )) (32))) ” 
  &&  “ ((s - 1 ) <= 31) ” 
  &&  “ (0 <= (s - 1 )) ”
).

Definition solver_safety_wit_10_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((signed_last_nbits ((1 * (2^(s - 1 )) )) (32)) <= INT_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^(s - 1 )) )) (32))) ”
.

Definition solver_safety_wit_10_split_goal_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((s - 1 ) <= 31) ”
.

Definition solver_safety_wit_10_split_goal_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (0 <= (s - 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((s - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s - 1 )) ”
.

Definition solver_safety_wit_12 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_14 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) (PreH24 : ((Z.land fam (signed_last_nbits ((Z.shiftl 1 (s - 1 ))) (32))) <> 0)) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((cnt + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cnt + 1 )) ”
.

Definition solver_safety_wit_15 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) (PreH24 : ((Z.land fam (signed_last_nbits ((Z.shiftl 1 (s - 1 ))) (32))) <> 0)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> (cnt + 1 ))
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) (PreH7 : (0 <= fam)) (PreH8 : (fam < 128)) (PreH9 : (0 <= best)) (PreH10 : (best <= 7)) (PreH11 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH12 : (1 <= s)) (PreH13 : (s <= 7)) (PreH14 : (1 <= cnt)) (PreH15 : (cnt <= 7)) (PreH16 : (0 <= d)) (PreH17 : (d <= 3)) (PreH18 : (0 <= need_a)) (PreH19 : (need_a <= 4)) (PreH20 : (0 <= need_b)) (PreH21 : (need_b <= 4)) (PreH22 : (0 <= need_c)) (PreH23 : (need_c <= 4)) (PreH24 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_17 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((signed_last_nbits ((1 * (2^d) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^d) )) (32))) ” 
  &&  “ (d <= 31) ” 
  &&  “ (0 <= d) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((signed_last_nbits ((1 * (2^d) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^d) )) (32))) ” 
  &&  “ (d <= 31) ” 
  &&  “ (0 <= d) ”
).

Definition solver_safety_wit_17_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((signed_last_nbits ((1 * (2^d) )) (32)) <= INT_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^d) )) (32))) ”
.

Definition solver_safety_wit_17_split_goal_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (d <= 31) ”
.

Definition solver_safety_wit_17_split_goal_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (0 <= d) ”
.

Definition solver_safety_wit_18 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (((Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0) + 1 )) ”
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (((Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0) + 1 )) ”
).

Definition solver_safety_wit_19_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ (((Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((INT_MIN) <= ((Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0) + 1 )) ”
.

Definition solver_safety_wit_20 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (replace_Znth (d) (((Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0) + 1 )) ((cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_21 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) = 0)) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition solver_safety_wit_22 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d >= 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((s + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) (PreH24 : ((Z.land fam (signed_last_nbits ((Z.shiftl 1 (s - 1 ))) (32))) = 0)) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ ((s + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s > 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_25 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_a <= a_pre)) (PreH2 : (s > 7)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 10)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 10)) (PreH7 : (0 <= c_pre)) (PreH8 : (c_pre <= 10)) (PreH9 : (0 <= fam)) (PreH10 : (fam < 128)) (PreH11 : (0 <= best)) (PreH12 : (best <= 7)) (PreH13 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH14 : (1 <= s)) (PreH15 : (s <= 8)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= 7)) (PreH18 : (0 <= need_a)) (PreH19 : (need_a <= 4)) (PreH20 : (0 <= need_b)) (PreH21 : (need_b <= 4)) (PreH22 : (0 <= need_c)) (PreH23 : (need_c <= 4)) (PreH24 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (IntArray.full ( &( "need" ) ) 3 (replace_Znth (0) (need_a) ((cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_26 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_b <= b_pre)) (PreH2 : (need_a <= a_pre)) (PreH3 : (s > 7)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 10)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 10)) (PreH8 : (0 <= c_pre)) (PreH9 : (c_pre <= 10)) (PreH10 : (0 <= fam)) (PreH11 : (fam < 128)) (PreH12 : (0 <= best)) (PreH13 : (best <= 7)) (PreH14 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH15 : (1 <= s)) (PreH16 : (s <= 8)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= 7)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (IntArray.full ( &( "need" ) ) 3 (replace_Znth (1) (need_b) ((replace_Znth (0) (need_a) ((cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_27 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt > best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> cnt)
|--
  “ ((fam + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fam + 1 )) ”
.

Definition solver_safety_wit_28 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_c > c_pre)) (PreH2 : (need_b <= b_pre)) (PreH3 : (need_a <= a_pre)) (PreH4 : (s > 7)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 10)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 10)) (PreH9 : (0 <= c_pre)) (PreH10 : (c_pre <= 10)) (PreH11 : (0 <= fam)) (PreH12 : (fam < 128)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7)) (PreH15 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH16 : (1 <= s)) (PreH17 : (s <= 8)) (PreH18 : (0 <= cnt)) (PreH19 : (cnt <= 7)) (PreH20 : (0 <= need_a)) (PreH21 : (need_a <= 4)) (PreH22 : (0 <= need_b)) (PreH23 : (need_b <= 4)) (PreH24 : (0 <= need_c)) (PreH25 : (need_c <= 4)) (PreH26 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((fam + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fam + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_a > a_pre)) (PreH2 : (s > 7)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 10)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 10)) (PreH7 : (0 <= c_pre)) (PreH8 : (c_pre <= 10)) (PreH9 : (0 <= fam)) (PreH10 : (fam < 128)) (PreH11 : (0 <= best)) (PreH12 : (best <= 7)) (PreH13 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH14 : (1 <= s)) (PreH15 : (s <= 8)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= 7)) (PreH18 : (0 <= need_a)) (PreH19 : (need_a <= 4)) (PreH20 : (0 <= need_b)) (PreH21 : (need_b <= 4)) (PreH22 : (0 <= need_c)) (PreH23 : (need_c <= 4)) (PreH24 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((fam + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fam + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_b > b_pre)) (PreH2 : (need_a <= a_pre)) (PreH3 : (s > 7)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 10)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 10)) (PreH8 : (0 <= c_pre)) (PreH9 : (c_pre <= 10)) (PreH10 : (0 <= fam)) (PreH11 : (fam < 128)) (PreH12 : (0 <= best)) (PreH13 : (best <= 7)) (PreH14 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH15 : (1 <= s)) (PreH16 : (s <= 8)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= 7)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((fam + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fam + 1 )) ”
.

Definition solver_safety_wit_31 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt <= best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
  **  ((( &( "fam" ) )) # Int  |-> fam)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((fam + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fam + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) ,
  TT && emp 
|--
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 128) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre 0 0 ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) ,
  TT && emp 
|--
  “ (BestBeforeMaskByBits a_pre b_pre c_pre 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (a_pre <= 10)) (PreH3 : (0 <= b_pre)) (PreH4 : (b_pre <= 10)) (PreH5 : (0 <= c_pre)) (PreH6 : (c_pre <= 10)) ,
  (BestBeforeMaskByBits a_pre b_pre c_pre 0 0 )
.

Definition solver_entail_wit_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam < 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  (IntArray.full ( &( "need" ) ) 3 (repeat_Z (0) (3)) )
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 7) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam 1 0 need_a need_b need_c ) ”
  &&  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam < 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  TT && emp 
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ ((repeat_Z (0) (3)) = (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z)))))))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 7) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam 1 0 need_a need_b need_c ) ”
  &&  emp
).

Definition solver_entail_wit_3 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a_2)) (PreH18 : (need_a_2 <= 4)) (PreH19 : (0 <= need_b_2)) (PreH20 : (need_b_2 <= 4)) (PreH21 : (0 <= need_c_2)) (PreH22 : (need_c_2 <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a_2 need_b_2 need_c_2 )) (PreH24 : ((Z.land fam (signed_last_nbits ((Z.shiftl 1 (s - 1 ))) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) )
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 7) ” 
  &&  “ (1 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) <= 7) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s 0 (cnt + 1 ) need_a need_b need_c ) ”
  &&  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a_2)) (PreH18 : (need_a_2 <= 4)) (PreH19 : (0 <= need_b_2)) (PreH20 : (need_b_2 <= 4)) (PreH21 : (0 <= need_c_2)) (PreH22 : (need_c_2 <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a_2 need_b_2 need_c_2 )) (PreH24 : ((Z.land fam (signed_last_nbits ((Z.shiftl 1 (s - 1 ))) (32))) <> 0)) ,
  TT && emp 
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ ((cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) = (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z)))))))) ” 
  &&  “ (1 <= (cnt + 1 )) ” 
  &&  “ ((cnt + 1 ) <= 7) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s 0 (cnt + 1 ) need_a need_b need_c ) ”
  &&  emp
).

Definition solver_entail_wit_4_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a_2)) (PreH20 : (need_a_2 <= 4)) (PreH21 : (0 <= need_b_2)) (PreH22 : (need_b_2 <= 4)) (PreH23 : (0 <= need_c_2)) (PreH24 : (need_c_2 <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a_2 need_b_2 need_c_2 )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (replace_Znth (d) (((Znth d (cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) 0) + 1 )) ((cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))))) )
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 7) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s (d + 1 ) cnt need_a need_b need_c ) ”
  &&  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a_2)) (PreH20 : (need_a_2 <= 4)) (PreH21 : (0 <= need_b_2)) (PreH22 : (need_b_2 <= 4)) (PreH23 : (0 <= need_c_2)) (PreH24 : (need_c_2 <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a_2 need_b_2 need_c_2 )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  TT && emp 
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ ((replace_Znth (d) (((Znth d (cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) 0) + 1 )) ((cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))))) = (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z)))))))) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s (d + 1 ) cnt need_a need_b need_c ) ”
  &&  emp
).

Definition solver_entail_wit_4_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a_2)) (PreH20 : (need_a_2 <= 4)) (PreH21 : (0 <= need_b_2)) (PreH22 : (need_b_2 <= 4)) (PreH23 : (0 <= need_c_2)) (PreH24 : (need_c_2 <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a_2 need_b_2 need_c_2 )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) = 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) )
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 7) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s (d + 1 ) cnt need_a need_b need_c ) ”
  &&  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a_2)) (PreH20 : (need_a_2 <= 4)) (PreH21 : (0 <= need_b_2)) (PreH22 : (need_b_2 <= 4)) (PreH23 : (0 <= need_c_2)) (PreH24 : (need_c_2 <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a_2 need_b_2 need_c_2 )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) = 0)) ,
  TT && emp 
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ ((cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) = (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z)))))))) ” 
  &&  “ (0 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s (d + 1 ) cnt need_a need_b need_c ) ”
  &&  emp
).

Definition solver_entail_wit_5_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d >= 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a_2)) (PreH20 : (need_a_2 <= 4)) (PreH21 : (0 <= need_b_2)) (PreH22 : (need_b_2 <= 4)) (PreH23 : (0 <= need_c_2)) (PreH24 : (need_c_2 <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a_2 need_b_2 need_c_2 )) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) )
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= 8) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam (s + 1 ) cnt need_a need_b need_c ) ”
  &&  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d >= 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a_2)) (PreH20 : (need_a_2 <= 4)) (PreH21 : (0 <= need_b_2)) (PreH22 : (need_b_2 <= 4)) (PreH23 : (0 <= need_c_2)) (PreH24 : (need_c_2 <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a_2 need_b_2 need_c_2 )) ,
  TT && emp 
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ ((cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) = (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z)))))))) ” 
  &&  “ (1 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= 8) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam (s + 1 ) cnt need_a need_b need_c ) ”
  &&  emp
).

Definition solver_entail_wit_5_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a_2)) (PreH18 : (need_a_2 <= 4)) (PreH19 : (0 <= need_b_2)) (PreH20 : (need_b_2 <= 4)) (PreH21 : (0 <= need_c_2)) (PreH22 : (need_c_2 <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a_2 need_b_2 need_c_2 )) (PreH24 : ((Z.land fam (signed_last_nbits ((Z.shiftl 1 (s - 1 ))) (32))) = 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) )
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= 8) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam (s + 1 ) cnt need_a need_b need_c ) ”
  &&  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c_2: Z) (need_b_2: Z) (need_a_2: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s <= 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a_2)) (PreH18 : (need_a_2 <= 4)) (PreH19 : (0 <= need_b_2)) (PreH20 : (need_b_2 <= 4)) (PreH21 : (0 <= need_c_2)) (PreH22 : (need_c_2 <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a_2 need_b_2 need_c_2 )) (PreH24 : ((Z.land fam (signed_last_nbits ((Z.shiftl 1 (s - 1 ))) (32))) = 0)) ,
  TT && emp 
|--
  EX (need_c: Z)  (need_b: Z)  (need_a: Z) ,
  “ ((cons (need_a_2) ((cons (need_b_2) ((cons (need_c_2) ((@nil Z))))))) = (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z)))))))) ” 
  &&  “ (1 <= (s + 1 )) ” 
  &&  “ ((s + 1 ) <= 8) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam (s + 1 ) cnt need_a need_b need_c ) ”
  &&  emp
).

Definition solver_entail_wit_6_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt > best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= (fam + 1 )) ” 
  &&  “ ((fam + 1 ) <= 128) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) cnt ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt > best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) cnt ) ”
  &&  emp
).

Definition solver_entail_wit_6_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt > best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) cnt )
.

Definition solver_entail_wit_6_2 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_c > c_pre)) (PreH2 : (need_b <= b_pre)) (PreH3 : (need_a <= a_pre)) (PreH4 : (s > 7)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 10)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 10)) (PreH9 : (0 <= c_pre)) (PreH10 : (c_pre <= 10)) (PreH11 : (0 <= fam)) (PreH12 : (fam < 128)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7)) (PreH15 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH16 : (1 <= s)) (PreH17 : (s <= 8)) (PreH18 : (0 <= cnt)) (PreH19 : (cnt <= 7)) (PreH20 : (0 <= need_a)) (PreH21 : (need_a <= 4)) (PreH22 : (0 <= need_b)) (PreH23 : (need_b <= 4)) (PreH24 : (0 <= need_c)) (PreH25 : (need_c <= 4)) (PreH26 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= (fam + 1 )) ” 
  &&  “ ((fam + 1 ) <= 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_c > c_pre)) (PreH2 : (need_b <= b_pre)) (PreH3 : (need_a <= a_pre)) (PreH4 : (s > 7)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 10)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 10)) (PreH9 : (0 <= c_pre)) (PreH10 : (c_pre <= 10)) (PreH11 : (0 <= fam)) (PreH12 : (fam < 128)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7)) (PreH15 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH16 : (1 <= s)) (PreH17 : (s <= 8)) (PreH18 : (0 <= cnt)) (PreH19 : (cnt <= 7)) (PreH20 : (0 <= need_a)) (PreH21 : (need_a <= 4)) (PreH22 : (0 <= need_b)) (PreH23 : (need_b <= 4)) (PreH24 : (0 <= need_c)) (PreH25 : (need_c <= 4)) (PreH26 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_6_2_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_c > c_pre)) (PreH2 : (need_b <= b_pre)) (PreH3 : (need_a <= a_pre)) (PreH4 : (s > 7)) (PreH5 : (0 <= a_pre)) (PreH6 : (a_pre <= 10)) (PreH7 : (0 <= b_pre)) (PreH8 : (b_pre <= 10)) (PreH9 : (0 <= c_pre)) (PreH10 : (c_pre <= 10)) (PreH11 : (0 <= fam)) (PreH12 : (fam < 128)) (PreH13 : (0 <= best)) (PreH14 : (best <= 7)) (PreH15 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH16 : (1 <= s)) (PreH17 : (s <= 8)) (PreH18 : (0 <= cnt)) (PreH19 : (cnt <= 7)) (PreH20 : (0 <= need_a)) (PreH21 : (need_a <= 4)) (PreH22 : (0 <= need_b)) (PreH23 : (need_b <= 4)) (PreH24 : (0 <= need_c)) (PreH25 : (need_c <= 4)) (PreH26 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best )
.

Definition solver_entail_wit_6_3 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_a > a_pre)) (PreH2 : (s > 7)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 10)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 10)) (PreH7 : (0 <= c_pre)) (PreH8 : (c_pre <= 10)) (PreH9 : (0 <= fam)) (PreH10 : (fam < 128)) (PreH11 : (0 <= best)) (PreH12 : (best <= 7)) (PreH13 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH14 : (1 <= s)) (PreH15 : (s <= 8)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= 7)) (PreH18 : (0 <= need_a)) (PreH19 : (need_a <= 4)) (PreH20 : (0 <= need_b)) (PreH21 : (need_b <= 4)) (PreH22 : (0 <= need_c)) (PreH23 : (need_c <= 4)) (PreH24 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= (fam + 1 )) ” 
  &&  “ ((fam + 1 ) <= 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_a > a_pre)) (PreH2 : (s > 7)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 10)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 10)) (PreH7 : (0 <= c_pre)) (PreH8 : (c_pre <= 10)) (PreH9 : (0 <= fam)) (PreH10 : (fam < 128)) (PreH11 : (0 <= best)) (PreH12 : (best <= 7)) (PreH13 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH14 : (1 <= s)) (PreH15 : (s <= 8)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= 7)) (PreH18 : (0 <= need_a)) (PreH19 : (need_a <= 4)) (PreH20 : (0 <= need_b)) (PreH21 : (need_b <= 4)) (PreH22 : (0 <= need_c)) (PreH23 : (need_c <= 4)) (PreH24 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_6_3_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_a > a_pre)) (PreH2 : (s > 7)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 10)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 10)) (PreH7 : (0 <= c_pre)) (PreH8 : (c_pre <= 10)) (PreH9 : (0 <= fam)) (PreH10 : (fam < 128)) (PreH11 : (0 <= best)) (PreH12 : (best <= 7)) (PreH13 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH14 : (1 <= s)) (PreH15 : (s <= 8)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= 7)) (PreH18 : (0 <= need_a)) (PreH19 : (need_a <= 4)) (PreH20 : (0 <= need_b)) (PreH21 : (need_b <= 4)) (PreH22 : (0 <= need_c)) (PreH23 : (need_c <= 4)) (PreH24 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best )
.

Definition solver_entail_wit_6_4 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_b > b_pre)) (PreH2 : (need_a <= a_pre)) (PreH3 : (s > 7)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 10)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 10)) (PreH8 : (0 <= c_pre)) (PreH9 : (c_pre <= 10)) (PreH10 : (0 <= fam)) (PreH11 : (fam < 128)) (PreH12 : (0 <= best)) (PreH13 : (best <= 7)) (PreH14 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH15 : (1 <= s)) (PreH16 : (s <= 8)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= 7)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= (fam + 1 )) ” 
  &&  “ ((fam + 1 ) <= 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_b > b_pre)) (PreH2 : (need_a <= a_pre)) (PreH3 : (s > 7)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 10)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 10)) (PreH8 : (0 <= c_pre)) (PreH9 : (c_pre <= 10)) (PreH10 : (0 <= fam)) (PreH11 : (fam < 128)) (PreH12 : (0 <= best)) (PreH13 : (best <= 7)) (PreH14 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH15 : (1 <= s)) (PreH16 : (s <= 8)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= 7)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_6_4_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_b > b_pre)) (PreH2 : (need_a <= a_pre)) (PreH3 : (s > 7)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 10)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 10)) (PreH8 : (0 <= c_pre)) (PreH9 : (c_pre <= 10)) (PreH10 : (0 <= fam)) (PreH11 : (fam < 128)) (PreH12 : (0 <= best)) (PreH13 : (best <= 7)) (PreH14 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH15 : (1 <= s)) (PreH16 : (s <= 8)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= 7)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best )
.

Definition solver_entail_wit_6_5 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt <= best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= (fam + 1 )) ” 
  &&  “ ((fam + 1 ) <= 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt <= best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  TT && emp 
|--
  “ (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best ) ”
  &&  emp
).

Definition solver_entail_wit_6_5_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (cnt <= best)) (PreH2 : (need_c <= c_pre)) (PreH3 : (need_b <= b_pre)) (PreH4 : (need_a <= a_pre)) (PreH5 : (s > 7)) (PreH6 : (0 <= a_pre)) (PreH7 : (a_pre <= 10)) (PreH8 : (0 <= b_pre)) (PreH9 : (b_pre <= 10)) (PreH10 : (0 <= c_pre)) (PreH11 : (c_pre <= 10)) (PreH12 : (0 <= fam)) (PreH13 : (fam < 128)) (PreH14 : (0 <= best)) (PreH15 : (best <= 7)) (PreH16 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH17 : (1 <= s)) (PreH18 : (s <= 8)) (PreH19 : (0 <= cnt)) (PreH20 : (cnt <= 7)) (PreH21 : (0 <= need_a)) (PreH22 : (need_a <= 4)) (PreH23 : (0 <= need_b)) (PreH24 : (need_b <= 4)) (PreH25 : (0 <= need_c)) (PreH26 : (need_c <= 4)) (PreH27 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (BestBeforeMaskByBits a_pre b_pre c_pre (fam + 1 ) best )
.

Definition solver_return_wit_1 := 
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam >= 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  TT && emp 
|--
  “ (Spec a_pre b_pre c_pre best ) ”
  &&  emp
) \/
(
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam >= 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  TT && emp 
|--
  “ (Spec a_pre b_pre c_pre best ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (best: Z) (fam: Z) (PreH1 : (fam >= 128)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam <= 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) ,
  (Spec a_pre b_pre c_pre best )
.

Definition solver_partial_solve_wit_1 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (d < 3) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 7) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c ) ” 
  &&  “ ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0) ”
  &&  (((( &( "need" ) ) + (d * sizeof(INT)))) # Int  |-> (Znth d (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) 0))
  **  (IntArray.missing_i ( &( "need" ) ) d 0 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
.

Definition solver_partial_solve_wit_2 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (d: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (d < 3)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 7)) (PreH15 : (1 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= d)) (PreH18 : (d <= 3)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c )) (PreH26 : ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0)) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (d < 3) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 7) ” 
  &&  “ (1 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 3) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (SelectedDishPrefixByBits fam s d cnt need_a need_b need_c ) ” 
  &&  “ ((Z.land s (signed_last_nbits ((Z.shiftl 1 d)) (32))) <> 0) ”
  &&  (((( &( "need" ) ) + (d * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "need" ) ) d 0 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
.

Definition solver_partial_solve_wit_3 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (s > 7)) (PreH2 : (0 <= a_pre)) (PreH3 : (a_pre <= 10)) (PreH4 : (0 <= b_pre)) (PreH5 : (b_pre <= 10)) (PreH6 : (0 <= c_pre)) (PreH7 : (c_pre <= 10)) (PreH8 : (0 <= fam)) (PreH9 : (fam < 128)) (PreH10 : (0 <= best)) (PreH11 : (best <= 7)) (PreH12 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH13 : (1 <= s)) (PreH14 : (s <= 8)) (PreH15 : (0 <= cnt)) (PreH16 : (cnt <= 7)) (PreH17 : (0 <= need_a)) (PreH18 : (need_a <= 4)) (PreH19 : (0 <= need_b)) (PreH20 : (need_b <= 4)) (PreH21 : (0 <= need_c)) (PreH22 : (need_c <= 4)) (PreH23 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (IntArray.full ( &( "need" ) ) 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
|--
  “ (s > 7) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 8) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam s cnt need_a need_b need_c ) ”
  &&  (((( &( "need" ) ) + (0 * sizeof(INT)))) # Int  |-> need_a)
  **  (IntArray.missing_i ( &( "need" ) ) 0 0 3 (cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))) )
.

Definition solver_partial_solve_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_a <= a_pre)) (PreH2 : (s > 7)) (PreH3 : (0 <= a_pre)) (PreH4 : (a_pre <= 10)) (PreH5 : (0 <= b_pre)) (PreH6 : (b_pre <= 10)) (PreH7 : (0 <= c_pre)) (PreH8 : (c_pre <= 10)) (PreH9 : (0 <= fam)) (PreH10 : (fam < 128)) (PreH11 : (0 <= best)) (PreH12 : (best <= 7)) (PreH13 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH14 : (1 <= s)) (PreH15 : (s <= 8)) (PreH16 : (0 <= cnt)) (PreH17 : (cnt <= 7)) (PreH18 : (0 <= need_a)) (PreH19 : (need_a <= 4)) (PreH20 : (0 <= need_b)) (PreH21 : (need_b <= 4)) (PreH22 : (0 <= need_c)) (PreH23 : (need_c <= 4)) (PreH24 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (IntArray.full ( &( "need" ) ) 3 (replace_Znth (0) (need_a) ((cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))))) )
|--
  “ (need_a <= a_pre) ” 
  &&  “ (s > 7) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 8) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam s cnt need_a need_b need_c ) ”
  &&  (((( &( "need" ) ) + (1 * sizeof(INT)))) # Int  |-> need_b)
  **  (IntArray.missing_i ( &( "need" ) ) 1 0 3 (replace_Znth (0) (need_a) ((cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))))) )
.

Definition solver_partial_solve_wit_5 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (need_c: Z) (need_b: Z) (need_a: Z) (cnt: Z) (s: Z) (best: Z) (fam: Z) (PreH1 : (need_b <= b_pre)) (PreH2 : (need_a <= a_pre)) (PreH3 : (s > 7)) (PreH4 : (0 <= a_pre)) (PreH5 : (a_pre <= 10)) (PreH6 : (0 <= b_pre)) (PreH7 : (b_pre <= 10)) (PreH8 : (0 <= c_pre)) (PreH9 : (c_pre <= 10)) (PreH10 : (0 <= fam)) (PreH11 : (fam < 128)) (PreH12 : (0 <= best)) (PreH13 : (best <= 7)) (PreH14 : (BestBeforeMaskByBits a_pre b_pre c_pre fam best )) (PreH15 : (1 <= s)) (PreH16 : (s <= 8)) (PreH17 : (0 <= cnt)) (PreH18 : (cnt <= 7)) (PreH19 : (0 <= need_a)) (PreH20 : (need_a <= 4)) (PreH21 : (0 <= need_b)) (PreH22 : (need_b <= 4)) (PreH23 : (0 <= need_c)) (PreH24 : (need_c <= 4)) (PreH25 : (FamilyPrefixByBits fam s cnt need_a need_b need_c )) ,
  (IntArray.full ( &( "need" ) ) 3 (replace_Znth (1) (need_b) ((replace_Znth (0) (need_a) ((cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))))))) )
|--
  “ (need_b <= b_pre) ” 
  &&  “ (need_a <= a_pre) ” 
  &&  “ (s > 7) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (a_pre <= 10) ” 
  &&  “ (0 <= b_pre) ” 
  &&  “ (b_pre <= 10) ” 
  &&  “ (0 <= c_pre) ” 
  &&  “ (c_pre <= 10) ” 
  &&  “ (0 <= fam) ” 
  &&  “ (fam < 128) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 7) ” 
  &&  “ (BestBeforeMaskByBits a_pre b_pre c_pre fam best ) ” 
  &&  “ (1 <= s) ” 
  &&  “ (s <= 8) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= 7) ” 
  &&  “ (0 <= need_a) ” 
  &&  “ (need_a <= 4) ” 
  &&  “ (0 <= need_b) ” 
  &&  “ (need_b <= 4) ” 
  &&  “ (0 <= need_c) ” 
  &&  “ (need_c <= 4) ” 
  &&  “ (FamilyPrefixByBits fam s cnt need_a need_b need_c ) ”
  &&  (((( &( "need" ) ) + (2 * sizeof(INT)))) # Int  |-> need_c)
  **  (IntArray.missing_i ( &( "need" ) ) 2 0 3 (replace_Znth (1) (need_b) ((replace_Znth (0) (need_a) ((cons (need_a) ((cons (need_b) ((cons (need_c) ((@nil Z))))))))))) )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Axiom proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Axiom proof_of_solver_entail_wit_6_3 : solver_entail_wit_6_3.
Axiom proof_of_solver_entail_wit_6_4 : solver_entail_wit_6_4.
Axiom proof_of_solver_entail_wit_6_5 : solver_entail_wit_6_5.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
