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
Require Import SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib.
Local Open Scope sac.

(*----- Function get_prime -----*)

Definition get_prime_safety_wit_1 := 
forall (prime_pre: Z) (flag_pre: Z) (tot_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1 ))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag0 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_prime_safety_wit_2 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1 ))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "tot" ) )) # Int  |-> 0)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag0 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_prime_safety_wit_3 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_prime_safety_wit_4 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l: (@list Z)) (tot: Z) (PreH1 : (tot = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (EulerOuterState n_pre 2 tot flag_l prime0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_prime_safety_wit_5 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ ((tot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tot + 1 )) ”
.

Definition get_prime_safety_wit_6 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_prime_safety_wit_7 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (EulerInnerState n_pre i 1 tot flag_l prime_l )) (PreH8 : (2 <= (Znth 0 prime_l 0))) (PreH9 : ((Znth 0 prime_l 0) <= i)) (PreH10 : ((i * (Znth 0 prime_l 0) ) <= INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_prime_safety_wit_8 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH10 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH11 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH12 : ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * (Znth (j - 1 ) prime_l 0) )) ”
.

Definition get_prime_safety_wit_9 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j > tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ False ”
.

Definition get_prime_safety_wit_10 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * (Znth (j - 1 ) prime_l 0) )) ”
.

Definition get_prime_safety_wit_11 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH12 : ((Znth (j - 1 ) prime_l 0) <= i)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ ((i <> (INT_MIN)) \/ ((Znth (j - 1 ) prime_l 0) <> (-1))) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <> 0) ”
.

Definition get_prime_safety_wit_12 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH12 : ((Znth (j - 1 ) prime_l 0) <= i)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_prime_safety_wit_13 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l prime_l )) (PreH10 : (2 <= (Znth j prime_l 0))) (PreH11 : ((Znth j prime_l 0) <= i)) (PreH12 : ((i * (Znth j prime_l 0) ) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition get_prime_safety_wit_14 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= tot)) (PreH6 : (tot < (i + 1 ))) (PreH7 : (EulerOuterState n_pre (i + 1 ) tot flag_l prime_l )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_prime_entail_wit_1 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1 ))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag0 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  EX (flag_l: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (EulerInitPrefix n_pre 2 flag_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
) \/
(
forall (n_pre: Z) (prime0: (@list Z)) (flag0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1 ))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  TT && emp 
|--
  “ (EulerInitPrefix n_pre 2 flag0 ) ”
  &&  emp
).

Definition get_prime_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (prime0: (@list Z)) (flag0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1 ))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  (EulerInitPrefix n_pre 2 flag0 )
.

Definition get_prime_entail_wit_2 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l_2)) )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  EX (flag_l: (@list Z)) ,
  “ (tot = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (EulerInitPrefix n_pre (i + 1 ) flag_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) ,
  TT && emp 
|--
  “ (EulerInitPrefix n_pre (i + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l_2)) ) ”
  &&  emp
).

Definition get_prime_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) ,
  (EulerInitPrefix n_pre (i + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l_2)) )
.

Definition get_prime_entail_wit_3 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i > n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  EX (flag_l: (@list Z)) ,
  “ (tot = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (EulerOuterState n_pre 2 tot flag_l prime0 ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
) \/
(
forall (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i > n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre 2 0 flag_l_2 prime0 ) ”
  &&  emp
).

Definition get_prime_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i > n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) ,
  (EulerOuterState n_pre 2 0 flag_l_2 prime0 )
.

Definition get_prime_entail_wit_4 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (tot: Z) (PreH1 : (tot = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (EulerOuterState n_pre 2 tot flag_l_2 prime0 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < 2) ” 
  &&  “ (EulerOuterState n_pre 2 tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_entail_wit_5_1 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (tot + 1 )) ” 
  &&  “ ((tot + 1 ) <= n_pre) ” 
  &&  “ (EulerInnerState n_pre i 1 (tot + 1 ) flag_l prime_l ) ” 
  &&  “ (2 <= (Znth 0 prime_l 0)) ” 
  &&  “ ((Znth 0 prime_l 0) <= i) ” 
  &&  “ ((i * (Znth 0 prime_l 0) ) <= INT_MAX) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  TT && emp 
|--
  “ ((i * (Znth 0 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0) ) <= INT_MAX) ” 
  &&  “ ((Znth 0 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0) <= i) ” 
  &&  “ (2 <= (Znth 0 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0)) ” 
  &&  “ (EulerInnerState n_pre i 1 (tot + 1 ) flag_l_2 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) ) ”
  &&  emp
).

Definition get_prime_entail_wit_5_1_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  ((i * (Znth 0 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0) ) <= INT_MAX)
.

Definition get_prime_entail_wit_5_1_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  ((Znth 0 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0) <= i)
.

Definition get_prime_entail_wit_5_1_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (2 <= (Znth 0 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0))
.

Definition get_prime_entail_wit_5_1_split_goal_4 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (EulerInnerState n_pre i 1 (tot + 1 ) flag_l_2 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) )
.

Definition get_prime_entail_wit_5_2 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerInnerState n_pre i 1 tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth 0 prime_l 0)) ” 
  &&  “ ((Znth 0 prime_l 0) <= i) ” 
  &&  “ ((i * (Znth 0 prime_l 0) ) <= INT_MAX) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  TT && emp 
|--
  “ ((i * (Znth 0 prime_l_2 0) ) <= INT_MAX) ” 
  &&  “ ((Znth 0 prime_l_2 0) <= i) ” 
  &&  “ (2 <= (Znth 0 prime_l_2 0)) ” 
  &&  “ (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2 ) ” 
  &&  “ (1 <= tot) ”
  &&  emp
).

Definition get_prime_entail_wit_5_2_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  ((i * (Znth 0 prime_l_2 0) ) <= INT_MAX)
.

Definition get_prime_entail_wit_5_2_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  ((Znth 0 prime_l_2 0) <= i)
.

Definition get_prime_entail_wit_5_2_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (2 <= (Znth 0 prime_l_2 0))
.

Definition get_prime_entail_wit_5_2_split_goal_4 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_5_2_split_goal_5 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (1 <= tot)
.

Definition get_prime_entail_wit_6 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2 )) (PreH8 : (2 <= (Znth 0 prime_l_2 0))) (PreH9 : ((Znth 0 prime_l_2 0) <= i)) (PreH10 : ((i * (Znth 0 prime_l_2 0) ) <= INT_MAX)) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (EulerInnerState n_pre i 1 tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (1 - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (1 - 1 ) prime_l 0) <= i) ” 
  &&  “ ((i * (Znth (1 - 1 ) prime_l 0) ) <= INT_MAX) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_entail_wit_7 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= INT_MAX)) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) (replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)) )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= tot) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre) ” 
  &&  “ (EulerInnerMarkedState n_pre i j tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (j - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <= i) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)) prime_l_2 ) ”
  &&  emp
).

Definition get_prime_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= INT_MAX)) ,
  (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)) prime_l_2 )
.

Definition get_prime_entail_wit_8 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= tot) ” 
  &&  “ (2 <= (Znth (j - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <= i) ” 
  &&  “ (EulerOuterState n_pre (i + 1 ) tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 ) ”
  &&  emp
).

Definition get_prime_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_9 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= tot) ” 
  &&  “ (EulerInnerState n_pre i (j + 1 ) tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth j prime_l 0)) ” 
  &&  “ ((Znth j prime_l 0) <= i) ” 
  &&  “ ((i * (Znth j prime_l 0) ) <= INT_MAX) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  TT && emp 
|--
  “ ((i * (Znth j prime_l_2 0) ) <= INT_MAX) ” 
  &&  “ ((Znth j prime_l_2 0) <= i) ” 
  &&  “ (2 <= (Znth j prime_l_2 0)) ” 
  &&  “ (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 ) ” 
  &&  “ ((j + 1 ) <= tot) ”
  &&  emp
).

Definition get_prime_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  ((i * (Znth j prime_l_2 0) ) <= INT_MAX)
.

Definition get_prime_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  ((Znth j prime_l_2 0) <= i)
.

Definition get_prime_entail_wit_9_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  (2 <= (Znth j prime_l_2 0))
.

Definition get_prime_entail_wit_9_split_goal_4 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_9_split_goal_5 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) ,
  ((j + 1 ) <= tot)
.

Definition get_prime_entail_wit_10 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((i * (Znth j prime_l_2 0) ) <= INT_MAX)) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= tot) ” 
  &&  “ (EulerInnerState n_pre i (j + 1 ) tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth ((j + 1 ) - 1 ) prime_l 0)) ” 
  &&  “ ((Znth ((j + 1 ) - 1 ) prime_l 0) <= i) ” 
  &&  “ ((i * (Znth ((j + 1 ) - 1 ) prime_l 0) ) <= INT_MAX) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((i * (Znth j prime_l_2 0) ) <= INT_MAX)) ,
  TT && emp 
|--
  “ ((i * (Znth ((j + 1 ) - 1 ) prime_l_2 0) ) <= INT_MAX) ” 
  &&  “ ((Znth ((j + 1 ) - 1 ) prime_l_2 0) <= i) ” 
  &&  “ (2 <= (Znth ((j + 1 ) - 1 ) prime_l_2 0)) ”
  &&  emp
).

Definition get_prime_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((i * (Znth j prime_l_2 0) ) <= INT_MAX)) ,
  ((i * (Znth ((j + 1 ) - 1 ) prime_l_2 0) ) <= INT_MAX)
.

Definition get_prime_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((i * (Znth j prime_l_2 0) ) <= INT_MAX)) ,
  ((Znth ((j + 1 ) - 1 ) prime_l_2 0) <= i)
.

Definition get_prime_entail_wit_10_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((i * (Znth j prime_l_2 0) ) <= INT_MAX)) ,
  (2 <= (Znth ((j + 1 ) - 1 ) prime_l_2 0))
.

Definition get_prime_entail_wit_11_1 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l_2 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH12 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH13 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= INT_MAX)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < (i + 1 )) ” 
  &&  “ (EulerOuterState n_pre (i + 1 ) tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l_2 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH12 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH13 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= INT_MAX)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 ) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  emp
).

Definition get_prime_entail_wit_11_1_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l_2 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH12 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH13 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= INT_MAX)) ,
  (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_11_1_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l_2 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH12 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH13 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= INT_MAX)) ,
  (tot < (i + 1 ))
.

Definition get_prime_entail_wit_11_2 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH10 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < (i + 1 )) ” 
  &&  “ (EulerOuterState n_pre (i + 1 ) tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH10 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )) ,
  TT && emp 
|--
  “ (tot < (i + 1 )) ”
  &&  emp
).

Definition get_prime_entail_wit_11_2_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH10 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )) ,
  (tot < (i + 1 ))
.

Definition get_prime_entail_wit_12 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= tot)) (PreH6 : (tot < (i + 1 ))) (PreH7 : (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < (i + 1 )) ” 
  &&  “ (EulerOuterState n_pre (i + 1 ) tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_entail_wit_13 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerOuterState n_pre (n_pre + 1 ) tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (n_pre + 1 ) tot flag_l_2 prime_l_2 ) ”
  &&  emp
).

Definition get_prime_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) ,
  (EulerOuterState n_pre (n_pre + 1 ) tot flag_l_2 prime_l_2 )
.

Definition get_prime_return_wit_1 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (0 <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerSieveResult n_pre tot flag_l_2 prime_l_2 )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 46340)) (PreH8 : (0 <= tot)) (PreH9 : (tot <= n_pre)) (PreH10 : (EulerOuterState n_pre (n_pre + 1 ) tot flag_l prime_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (final_tot: Z)  (flag_out: (@list Z))  (prime_out: (@list Z)) ,
  “ (prime_pre = prime_pre) ” 
  &&  “ (EulerSieveResult n_pre final_tot flag_out prime_out ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_out )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_out )
.

Definition get_prime_partial_solve_wit_1 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ (i <= n_pre) ” 
  &&  “ (tot = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (EulerInitPrefix n_pre i flag_l ) ”
  &&  (((flag_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i flag_pre i 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
.

Definition get_prime_partial_solve_wit_2 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (i <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < i) ” 
  &&  “ (EulerOuterState n_pre i tot flag_l prime_l ) ”
  &&  (((flag_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 2 ) flag_l 0))
  **  (IntArray.missing_i flag_pre i 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_partial_solve_wit_3 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ ((Znth (i - 2 ) flag_l 0) = i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < i) ” 
  &&  “ (EulerOuterState n_pre i tot flag_l prime_l ) ”
  &&  (((prime_pre + ((tot + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i prime_pre (tot + 1 ) 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
.

Definition get_prime_partial_solve_wit_4 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH10 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH11 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH12 : ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX)) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= tot) ” 
  &&  “ (EulerInnerState n_pre i j tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (j - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <= i) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
.

Definition get_prime_partial_solve_wit_5 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ (j <= tot) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= tot) ” 
  &&  “ (EulerInnerState n_pre i j tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (j - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <= i) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
.

Definition get_prime_partial_solve_wit_6 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ (j <= tot) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= tot) ” 
  &&  “ (EulerInnerState n_pre i j tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (j - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <= i) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
.

Definition get_prime_partial_solve_wit_7 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
|--
  “ (j <= tot) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= tot) ” 
  &&  “ (EulerInnerState n_pre i j tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (j - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <= i) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ”
  &&  (((flag_pre + ((i * (Znth (j - 1 ) prime_l 0) ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i flag_pre (i * (Znth (j - 1 ) prime_l 0) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_partial_solve_wit_8 := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH12 : ((Znth (j - 1 ) prime_l 0) <= i)) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= tot) ” 
  &&  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre) ” 
  &&  “ (EulerInnerMarkedState n_pre i j tot flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (j - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <= i) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
.

Definition get_prime_partial_solve_wit_9_pure := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (0 <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1 ) tot flag_l prime_l )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "flag" ) )) # Ptr  |-> flag_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerOuterState n_pre (n_pre + 1 ) tot flag_l prime_l ) ”
.

Definition get_prime_partial_solve_wit_9_aux := 
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (0 <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1 ) tot flag_l prime_l )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerOuterState n_pre (n_pre + 1 ) tot flag_l prime_l ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerOuterState n_pre (n_pre + 1 ) tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_partial_solve_wit_9 := get_prime_partial_solve_wit_9_pure -> get_prime_partial_solve_wit_9_aux.

Definition get_prime_which_implies_wit_1 := 
(
forall (prime_pre: Z) (flag_pre: Z) (n_pre: Z) (prime_l_2: (@list Z)) (flag_l_2: (@list Z)) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (0 <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1 ) tot flag_l_2 prime_l_2 )) ,
  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerSieveResult n_pre tot flag_l prime_l ) ”
  &&  (IntArray.seg flag_pre 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (prime_l_2: (@list Z)) (flag_l_2: (@list Z)) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (0 <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1 ) tot flag_l_2 prime_l_2 )) ,
  TT && emp 
|--
  “ (EulerSieveResult n_pre tot flag_l_2 prime_l_2 ) ”
  &&  emp
).

Definition get_prime_which_implies_wit_1_split_goal_1 := 
forall (n_pre: Z) (prime_l_2: (@list Z)) (flag_l_2: (@list Z)) (tot: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (0 <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1 ) tot flag_l_2 prime_l_2 )) ,
  (EulerSieveResult n_pre tot flag_l_2 prime_l_2 )
.

Module Type VC_Correct.


Axiom proof_of_get_prime_safety_wit_1 : get_prime_safety_wit_1.
Axiom proof_of_get_prime_safety_wit_2 : get_prime_safety_wit_2.
Axiom proof_of_get_prime_safety_wit_3 : get_prime_safety_wit_3.
Axiom proof_of_get_prime_safety_wit_4 : get_prime_safety_wit_4.
Axiom proof_of_get_prime_safety_wit_5 : get_prime_safety_wit_5.
Axiom proof_of_get_prime_safety_wit_6 : get_prime_safety_wit_6.
Axiom proof_of_get_prime_safety_wit_7 : get_prime_safety_wit_7.
Axiom proof_of_get_prime_safety_wit_8 : get_prime_safety_wit_8.
Axiom proof_of_get_prime_safety_wit_9 : get_prime_safety_wit_9.
Axiom proof_of_get_prime_safety_wit_10 : get_prime_safety_wit_10.
Axiom proof_of_get_prime_safety_wit_11 : get_prime_safety_wit_11.
Axiom proof_of_get_prime_safety_wit_12 : get_prime_safety_wit_12.
Axiom proof_of_get_prime_safety_wit_13 : get_prime_safety_wit_13.
Axiom proof_of_get_prime_safety_wit_14 : get_prime_safety_wit_14.
Axiom proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1.
Axiom proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2.
Axiom proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3.
Axiom proof_of_get_prime_entail_wit_4 : get_prime_entail_wit_4.
Axiom proof_of_get_prime_entail_wit_5_1 : get_prime_entail_wit_5_1.
Axiom proof_of_get_prime_entail_wit_5_2 : get_prime_entail_wit_5_2.
Axiom proof_of_get_prime_entail_wit_6 : get_prime_entail_wit_6.
Axiom proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7.
Axiom proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8.
Axiom proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9.
Axiom proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10.
Axiom proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1.
Axiom proof_of_get_prime_entail_wit_11_2 : get_prime_entail_wit_11_2.
Axiom proof_of_get_prime_entail_wit_12 : get_prime_entail_wit_12.
Axiom proof_of_get_prime_entail_wit_13 : get_prime_entail_wit_13.
Axiom proof_of_get_prime_return_wit_1 : get_prime_return_wit_1.
Axiom proof_of_get_prime_partial_solve_wit_1 : get_prime_partial_solve_wit_1.
Axiom proof_of_get_prime_partial_solve_wit_2 : get_prime_partial_solve_wit_2.
Axiom proof_of_get_prime_partial_solve_wit_3 : get_prime_partial_solve_wit_3.
Axiom proof_of_get_prime_partial_solve_wit_4 : get_prime_partial_solve_wit_4.
Axiom proof_of_get_prime_partial_solve_wit_5 : get_prime_partial_solve_wit_5.
Axiom proof_of_get_prime_partial_solve_wit_6 : get_prime_partial_solve_wit_6.
Axiom proof_of_get_prime_partial_solve_wit_7 : get_prime_partial_solve_wit_7.
Axiom proof_of_get_prime_partial_solve_wit_8 : get_prime_partial_solve_wit_8.
Axiom proof_of_get_prime_partial_solve_wit_9_pure : get_prime_partial_solve_wit_9_pure.
Axiom proof_of_get_prime_partial_solve_wit_9 : get_prime_partial_solve_wit_9.
Axiom proof_of_get_prime_which_implies_wit_1 : get_prime_which_implies_wit_1.

End VC_Correct.
