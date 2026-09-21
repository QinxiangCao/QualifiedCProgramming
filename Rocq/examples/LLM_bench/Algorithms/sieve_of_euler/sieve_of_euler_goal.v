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
forall (prime_pre: Z) (tot_pre: Z) (n_pre: Z) (prime0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "z" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "flag" ) ) 46341 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_prime_safety_wit_2 := 
forall (prime_pre: Z) (tot_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_init: (@list Z)) (z: Z) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init)) = (z - 2 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 z flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) z (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_prime_safety_wit_3 := 
forall (prime_pre: Z) (tot_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_init: (@list Z)) (z: Z) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init)) = (z - 2 ))) ,
  (IntArray.seg ( &( "flag" ) ) 2 (z + 1 ) (app (flag_init) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (z + 1 ) (n_pre + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition get_prime_safety_wit_4 := 
forall (prime_pre: Z) (tot_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_init: (@list Z)) (z: Z) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init)) = (z - 2 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot_pre)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 z flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) z (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_prime_safety_wit_5 := 
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_init: (@list Z)) (z: Z) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init)) = (z - 2 ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> 0)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 z flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) z (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_prime_safety_wit_6 := 
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l )) (PreH8 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_prime_safety_wit_7 := 
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i > n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l )) (PreH8 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition get_prime_safety_wit_8 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ ((tot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tot + 1 )) ”
.

Definition get_prime_safety_wit_9 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_prime_safety_wit_10 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l)) )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> (tot + 1 ))
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_prime_safety_wit_11 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_prime_safety_wit_12 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH10 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH11 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * (Znth (j - 1 ) prime_l 0) )) ”
.

Definition get_prime_safety_wit_13 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j > tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ False ”
.

Definition get_prime_safety_wit_14 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ ((i * (Znth (j - 1 ) prime_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * (Znth (j - 1 ) prime_l 0) )) ”
.

Definition get_prime_safety_wit_15 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH12 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1 ))) (PreH16 : (~((Z.divide (Znth (j - 1 ) prime_l 0) i )) -> ((j + 1 ) <= tot))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ ((i <> (INT_MIN)) \/ ((Znth (j - 1 ) prime_l 0) <> (-1))) ” 
  &&  “ ((Znth (j - 1 ) prime_l 0) <> 0) ”
.

Definition get_prime_safety_wit_16 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH12 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1 ))) (PreH16 : (~((Z.divide (Znth (j - 1 ) prime_l 0) i )) -> ((j + 1 ) <= tot))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_prime_safety_wit_17 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l prime_l )) (PreH10 : (2 <= (Znth j prime_l 0))) (PreH11 : ((Znth j prime_l 0) <= i)) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (tot < (i + 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition get_prime_safety_wit_18 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH12 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_prime_safety_wit_19 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH10 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1 ) tot flag_l prime_l )) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (2 <= (i + 1 ))) (PreH15 : ((i + 1 ) <= (n_pre + 1 ))) (PreH16 : (0 <= tot)) (PreH17 : (tot < (i + 1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "prime" ) )) # Ptr  |-> prime_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tot" ) )) # Int  |-> tot)
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_prime_entail_wit_1 := 
(
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.undef_full ( &( "flag" ) ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  EX (flag_init: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ ((Zlength (prime0)) = n_pre) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (flag_init)) = (2 - 2 )) ”
  &&  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 2 flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) 2 (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
) \/
(
forall (n_pre: Z) (prime0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.undef_full ( &( "flag" ) ) 46341 )
|--
  “ ((Zlength ((@nil Z))) = (2 - 2 )) ”
  &&  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 2 (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
).

Definition get_prime_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (prime0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.undef_full ( &( "flag" ) ) 46341 )
|--
  “ ((Zlength ((@nil Z))) = (2 - 2 )) ”
.

Definition get_prime_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (prime0: (@list Z)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.undef_full ( &( "flag" ) ) 46341 )
|--
  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 2 (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
.

Definition get_prime_entail_wit_2 := 
(
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_init_2: (@list Z)) (z: Z) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init_2)) = (z - 2 ))) ,
  (IntArray.seg ( &( "flag" ) ) 2 (z + 1 ) (app (flag_init_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (z + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  EX (flag_init: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ ((Zlength (prime0)) = n_pre) ” 
  &&  “ (2 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (flag_init)) = ((z + 1 ) - 2 )) ”
  &&  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 (z + 1 ) flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) (z + 1 ) (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
) \/
(
forall (n_pre: Z) (prime0: (@list Z)) (flag_init_2: (@list Z)) (z: Z) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init_2)) = (z - 2 ))) ,
  TT && emp 
|--
  “ ((Zlength ((app (flag_init_2) ((cons (0) ((@nil Z))))))) = ((z + 1 ) - 2 )) ”
  &&  emp
).

Definition get_prime_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (prime0: (@list Z)) (flag_init_2: (@list Z)) (z: Z) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init_2)) = (z - 2 ))) ,
  ((Zlength ((app (flag_init_2) ((cons (0) ((@nil Z))))))) = ((z + 1 ) - 2 ))
.

Definition get_prime_entail_wit_3 := 
(
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_init: (@list Z)) (z: Z) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init)) = (z - 2 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 z flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) z (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  EX (flag_l: (@list Z)) ,
  “ (0 = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (EulerInitPrefix n_pre 2 flag_l ) ” 
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime0)) = n_pre) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
) \/
(
forall (n_pre: Z) (prime0: (@list Z)) (flag_init: (@list Z)) (z: Z) (PreH1 : (z > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init)) = (z - 2 ))) ,
  (IntArray.seg ( &( "flag" ) ) 2 z flag_init )
|--
  EX (flag_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (EulerInitPrefix n_pre 2 flag_l ) ” 
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime0)) = n_pre) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
).

Definition get_prime_entail_wit_4 := 
(
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l_2)) )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  EX (flag_l: (@list Z)) ,
  “ (tot = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (EulerInitPrefix n_pre (i + 1 ) flag_l ) ” 
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime0)) = n_pre) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
) \/
(
forall (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth ((i - 2 )) (i) (flag_l_2)))) = (n_pre - 1 )) ” 
  &&  “ (EulerInitPrefix n_pre (i + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l_2)) ) ”
  &&  emp
).

Definition get_prime_entail_wit_4_split_goal_1 := 
forall (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  ((Zlength ((replace_Znth ((i - 2 )) (i) (flag_l_2)))) = (n_pre - 1 ))
.

Definition get_prime_entail_wit_4_split_goal_2 := 
forall (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (EulerInitPrefix n_pre (i + 1 ) (replace_Znth ((i - 2 )) (i) (flag_l_2)) )
.

Definition get_prime_entail_wit_5 := 
(
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i > n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i > n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre 2 0 flag_l_2 prime0 ) ”
  &&  emp
).

Definition get_prime_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (prime0: (@list Z)) (flag_l_2: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i > n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2 )) (PreH8 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (EulerOuterState n_pre 2 0 flag_l_2 prime0 )
.

Definition get_prime_entail_wit_6_1 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (tot + 1 )) ” 
  &&  “ ((tot + 1 ) <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (tot + 1 )) ” 
  &&  “ (EulerInnerState n_pre i 1 (tot + 1 ) flag_l prime_l ) ” 
  &&  “ (2 <= (Znth (1 - 1 ) prime_l 0)) ” 
  &&  “ ((Znth (1 - 1 ) prime_l 0) <= i) ” 
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ ((tot + 1 ) < (i + 1 )) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  TT && emp 
|--
  “ ((Zlength ((replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)))) = n_pre) ” 
  &&  “ ((Znth (1 - 1 ) (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0) <= i) ” 
  &&  “ (2 <= (Znth (1 - 1 ) (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0)) ” 
  &&  “ (EulerInnerState n_pre i 1 (tot + 1 ) flag_l_2 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) ) ”
  &&  emp
).

Definition get_prime_entail_wit_6_1_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  ((Zlength ((replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)))) = n_pre)
.

Definition get_prime_entail_wit_6_1_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  ((Znth (1 - 1 ) (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0) <= i)
.

Definition get_prime_entail_wit_6_1_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (2 <= (Znth (1 - 1 ) (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) 0))
.

Definition get_prime_entail_wit_6_1_split_goal_4 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (EulerInnerState n_pre i 1 (tot + 1 ) flag_l_2 (replace_Znth (((tot + 1 ) - 1 )) (i) (prime_l_2)) )
.

Definition get_prime_entail_wit_6_2 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  TT && emp 
|--
  “ ((Znth (1 - 1 ) prime_l_2 0) <= i) ” 
  &&  “ (2 <= (Znth (1 - 1 ) prime_l_2 0)) ” 
  &&  “ (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2 ) ” 
  &&  “ (1 <= tot) ” 
  &&  “ (1 <= tot) ”
  &&  emp
).

Definition get_prime_entail_wit_6_2_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  ((Znth (1 - 1 ) prime_l_2 0) <= i)
.

Definition get_prime_entail_wit_6_2_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (2 <= (Znth (1 - 1 ) prime_l_2 0))
.

Definition get_prime_entail_wit_6_2_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_6_2_split_goal_4 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (1 <= tot)
.

Definition get_prime_entail_wit_6_2_split_goal_5 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l_2 0) <> i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2 )) (PreH10 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l_2)) = n_pre)) ,
  (1 <= tot)
.

Definition get_prime_entail_wit_7 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) (replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)) )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ” 
  &&  “ (~((Z.divide (Znth (j - 1 ) prime_l 0) i )) -> ((j + 1 ) <= tot)) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  TT && emp 
|--
  “ (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot)) ” 
  &&  “ ((Zlength ((replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)))) = (n_pre - 1 )) ” 
  &&  “ (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)) prime_l_2 ) ”
  &&  emp
).

Definition get_prime_entail_wit_7_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))
.

Definition get_prime_entail_wit_7_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  ((Zlength ((replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)))) = (n_pre - 1 ))
.

Definition get_prime_entail_wit_7_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1 ) prime_l_2 0) ) - 2 )) ((Znth (j - 1 ) prime_l_2 0)) (flag_l_2)) prime_l_2 )
.

Definition get_prime_entail_wit_8 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 ) ”
  &&  emp
).

Definition get_prime_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_9 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  TT && emp 
|--
  “ ((Znth j prime_l_2 0) <= i) ” 
  &&  “ (2 <= (Znth j prime_l_2 0)) ” 
  &&  “ (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 ) ” 
  &&  “ ((j + 1 ) <= tot) ”
  &&  emp
).

Definition get_prime_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  ((Znth j prime_l_2 0) <= i)
.

Definition get_prime_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  (2 <= (Znth j prime_l_2 0))
.

Definition get_prime_entail_wit_9_split_goal_3 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_9_split_goal_4 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : ((i % ( (Znth (j - 1 ) prime_l_2 0) ) ) <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1 ) prime_l_2 0) ) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2 )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH13 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH14 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l_2)) = n_pre)) (PreH16 : (tot < (i + 1 ))) (PreH17 : (~((Z.divide (Znth (j - 1 ) prime_l_2 0) i )) -> ((j + 1 ) <= tot))) ,
  ((j + 1 ) <= tot)
.

Definition get_prime_entail_wit_10 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1 ))) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1 ))) ,
  TT && emp 
|--
  “ ((Znth ((j + 1 ) - 1 ) prime_l_2 0) <= i) ” 
  &&  “ (2 <= (Znth ((j + 1 ) - 1 ) prime_l_2 0)) ”
  &&  emp
).

Definition get_prime_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1 ))) ,
  ((Znth ((j + 1 ) - 1 ) prime_l_2 0) <= i)
.

Definition get_prime_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1 ))) (PreH8 : ((j + 1 ) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1 ) tot flag_l_2 prime_l_2 )) (PreH10 : (2 <= (Znth j prime_l_2 0))) (PreH11 : ((Znth j prime_l_2 0) <= i)) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (tot < (i + 1 ))) ,
  (2 <= (Znth ((j + 1 ) - 1 ) prime_l_2 0))
.

Definition get_prime_entail_wit_11_1 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l_2 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH12 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH13 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (prime_l_2)) = n_pre)) (PreH15 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l_2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  EX (flag_l: (@list Z))  (prime_l: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= tot) ” 
  &&  “ (tot < (i + 1 )) ” 
  &&  “ (EulerOuterState n_pre (i + 1 ) tot flag_l prime_l ) ” 
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
) \/
(
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l_2 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH12 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH13 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (prime_l_2)) = n_pre)) (PreH15 : (tot < (i + 1 ))) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 ) ”
  &&  emp
).

Definition get_prime_entail_wit_11_1_split_goal_1 := 
forall (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : ((i * (Znth (j - 1 ) prime_l_2 0) ) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2 )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH12 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH13 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH14 : ((Zlength (prime_l_2)) = n_pre)) (PreH15 : (tot < (i + 1 ))) ,
  (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )
.

Definition get_prime_entail_wit_11_2 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l_2: (@list Z)) (prime_l_2: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1 ) prime_l_2 0))) (PreH10 : ((Znth (j - 1 ) prime_l_2 0) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1 ) tot flag_l_2 prime_l_2 )) (PreH12 : ((Zlength (flag_l_2)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l_2)) = n_pre)) (PreH14 : (2 <= (i + 1 ))) (PreH15 : ((i + 1 ) <= (n_pre + 1 ))) (PreH16 : (0 <= tot)) (PreH17 : (tot < (i + 1 ))) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l_2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_entail_wit_12 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH9 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH10 : ((Zlength (prime_l)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
|--
  EX (flag_out: (@list Z))  (prime_out: (@list Z)) ,
  “ (0 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerSieveResult n_pre tot flag_out prime_out ) ”
  &&  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_out )
  **  (IntArray.undef_full ( &( "flag" ) ) 46341 )
) \/
(
forall (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH9 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH10 : ((Zlength (prime_l)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  EX (flag_out: (@list Z)) ,
  “ (0 <= tot) ” 
  &&  “ (tot <= n_pre) ” 
  &&  “ (EulerSieveResult n_pre tot flag_out prime_l ) ”
  &&  (IntArray.undef_full ( &( "flag" ) ) 46341 )
).

Definition get_prime_return_wit_1 := 
(
forall (prime_pre: Z) (n_pre: Z) (flag_out: (@list Z)) (prime_out_2: (@list Z)) (tot: Z) (PreH1 : (0 <= tot)) (PreH2 : (tot <= n_pre)) (PreH3 : (EulerSieveResult n_pre tot flag_out prime_out_2 )) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_out_2 )
|--
  EX (prime_out: (@list Z))  (final_tot: Z) ,
  “ (prime_pre = prime_pre) ” 
  &&  “ (0 <= final_tot) ” 
  &&  “ (final_tot <= n_pre) ” 
  &&  “ (Modern.PrimePrefixList n_pre final_tot prime_out ) ”
  &&  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_out )
) \/
(
forall (n_pre: Z) (flag_out: (@list Z)) (prime_out_2: (@list Z)) (tot: Z) (PreH1 : (0 <= tot)) (PreH2 : (tot <= n_pre)) (PreH3 : (EulerSieveResult n_pre tot flag_out prime_out_2 )) ,
  TT && emp 
|--
  EX (final_tot: Z) ,
  “ (0 <= final_tot) ” 
  &&  “ (final_tot <= n_pre) ” 
  &&  “ (Modern.PrimePrefixList n_pre final_tot prime_out_2 ) ”
  &&  emp
).

Definition get_prime_partial_solve_wit_1 := 
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_init: (@list Z)) (z: Z) (PreH1 : (z <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : ((Zlength (prime0)) = n_pre)) (PreH5 : (2 <= z)) (PreH6 : (z <= (n_pre + 1 ))) (PreH7 : ((Zlength (flag_init)) = (z - 2 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 z flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) z (n_pre + 1 ) )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
|--
  “ (z <= n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ ((Zlength (prime0)) = n_pre) ” 
  &&  “ (2 <= z) ” 
  &&  “ (z <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (flag_init)) = (z - 2 )) ”
  &&  (((( &( "flag" ) ) + (z * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "flag" ) ) (z + 1 ) (n_pre + 1 ) )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.seg ( &( "flag" ) ) 2 z flag_init )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
.

Definition get_prime_partial_solve_wit_2 := 
forall (prime_pre: Z) (n_pre: Z) (prime0: (@list Z)) (flag_l: (@list Z)) (i: Z) (tot: Z) (PreH1 : (i <= n_pre)) (PreH2 : (tot = 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (EulerInitPrefix n_pre i flag_l )) (PreH8 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH9 : ((Zlength (prime0)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
|--
  “ (i <= n_pre) ” 
  &&  “ (tot = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (EulerInitPrefix n_pre i flag_l ) ” 
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime0)) = n_pre) ”
  &&  (((( &( "flag" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "flag" ) ) i 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime0 )
.

Definition get_prime_partial_solve_wit_3 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1 ))) (PreH6 : (0 <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH9 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH10 : ((Zlength (prime_l)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (((( &( "flag" ) ) + (i * sizeof(INT)))) # Int  |-> (Znth (i - 2 ) flag_l 0))
  **  (IntArray.missing_i ( &( "flag" ) ) i 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
.

Definition get_prime_partial_solve_wit_4 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (tot: Z) (i: Z) (PreH1 : ((Znth (i - 2 ) flag_l 0) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1 ))) (PreH7 : (0 <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l )) (PreH10 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH11 : ((Zlength (prime_l)) = n_pre)) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ”
  &&  (((prime_pre + ((tot + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i prime_pre (tot + 1 ) 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
.

Definition get_prime_partial_solve_wit_5 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH10 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH11 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH12 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH13 : ((Zlength (prime_l)) = n_pre)) (PreH14 : (tot < (i + 1 ))) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
.

Definition get_prime_partial_solve_wit_6 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
.

Definition get_prime_partial_solve_wit_7 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
.

Definition get_prime_partial_solve_wit_8 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (j: Z) (tot: Z) (i: Z) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l )) (PreH12 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH13 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH14 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH15 : ((Zlength (prime_l)) = n_pre)) (PreH16 : (tot < (i + 1 ))) ,
  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ”
  &&  (((( &( "flag" ) ) + ((i * (Znth (j - 1 ) prime_l 0) ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "flag" ) ) (i * (Znth (j - 1 ) prime_l 0) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.seg prime_pre 1 (n_pre + 1 ) prime_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
.

Definition get_prime_partial_solve_wit_9 := 
forall (prime_pre: Z) (n_pre: Z) (flag_l: (@list Z)) (prime_l: (@list Z)) (i: Z) (tot: Z) (j: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1 ) prime_l 0) ) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l )) (PreH11 : (2 <= (Znth (j - 1 ) prime_l 0))) (PreH12 : ((Znth (j - 1 ) prime_l 0) <= i)) (PreH13 : ((Zlength (flag_l)) = (n_pre - 1 ))) (PreH14 : ((Zlength (prime_l)) = n_pre)) (PreH15 : (tot < (i + 1 ))) (PreH16 : (~((Z.divide (Znth (j - 1 ) prime_l 0) i )) -> ((j + 1 ) <= tot))) ,
  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
  &&  “ ((Zlength (flag_l)) = (n_pre - 1 )) ” 
  &&  “ ((Zlength (prime_l)) = n_pre) ” 
  &&  “ (tot < (i + 1 )) ” 
  &&  “ (~((Z.divide (Znth (j - 1 ) prime_l 0) i )) -> ((j + 1 ) <= tot)) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) prime_l 0))
  **  (IntArray.missing_i prime_pre j 1 (n_pre + 1 ) prime_l )
  **  (IntArray.seg ( &( "flag" ) ) 2 (n_pre + 1 ) flag_l )
  **  (IntArray.undef_seg ( &( "flag" ) ) 0 2 )
  **  (IntArray.undef_seg ( &( "flag" ) ) (n_pre + 1 ) 46341 )
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
Axiom proof_of_get_prime_safety_wit_15 : get_prime_safety_wit_15.
Axiom proof_of_get_prime_safety_wit_16 : get_prime_safety_wit_16.
Axiom proof_of_get_prime_safety_wit_17 : get_prime_safety_wit_17.
Axiom proof_of_get_prime_safety_wit_18 : get_prime_safety_wit_18.
Axiom proof_of_get_prime_safety_wit_19 : get_prime_safety_wit_19.
Axiom proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1.
Axiom proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2.
Axiom proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3.
Axiom proof_of_get_prime_entail_wit_4 : get_prime_entail_wit_4.
Axiom proof_of_get_prime_entail_wit_5 : get_prime_entail_wit_5.
Axiom proof_of_get_prime_entail_wit_6_1 : get_prime_entail_wit_6_1.
Axiom proof_of_get_prime_entail_wit_6_2 : get_prime_entail_wit_6_2.
Axiom proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7.
Axiom proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8.
Axiom proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9.
Axiom proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10.
Axiom proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1.
Axiom proof_of_get_prime_entail_wit_11_2 : get_prime_entail_wit_11_2.
Axiom proof_of_get_prime_entail_wit_12 : get_prime_entail_wit_12.
Axiom proof_of_get_prime_return_wit_1 : get_prime_return_wit_1.
Axiom proof_of_get_prime_partial_solve_wit_1 : get_prime_partial_solve_wit_1.
Axiom proof_of_get_prime_partial_solve_wit_2 : get_prime_partial_solve_wit_2.
Axiom proof_of_get_prime_partial_solve_wit_3 : get_prime_partial_solve_wit_3.
Axiom proof_of_get_prime_partial_solve_wit_4 : get_prime_partial_solve_wit_4.
Axiom proof_of_get_prime_partial_solve_wit_5 : get_prime_partial_solve_wit_5.
Axiom proof_of_get_prime_partial_solve_wit_6 : get_prime_partial_solve_wit_6.
Axiom proof_of_get_prime_partial_solve_wit_7 : get_prime_partial_solve_wit_7.
Axiom proof_of_get_prime_partial_solve_wit_8 : get_prime_partial_solve_wit_8.
Axiom proof_of_get_prime_partial_solve_wit_9 : get_prime_partial_solve_wit_9.

End VC_Correct.
