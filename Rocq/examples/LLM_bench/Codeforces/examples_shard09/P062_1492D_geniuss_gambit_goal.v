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
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P062_1492D_geniuss_gambit_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (1 <= b_pre)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= (a_pre + b_pre ))) (PreH5 : ((a_pre + b_pre ) <= 200000)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (CharArray.undef_full x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.undef_full y_pre ((a_pre + b_pre ) + 1 ) )
|--
  “ ((a_pre + b_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a_pre + b_pre )) ”
.

Definition solver_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (1 <= b_pre)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= (a_pre + b_pre ))) (PreH5 : ((a_pre + b_pre ) <= 200000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (a_pre + b_pre ))
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (CharArray.undef_full x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.undef_full y_pre ((a_pre + b_pre ) + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  (CharArray.full x_pre (i + 1 ) (app ((repeat_Z (49) (i))) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg x_pre (i + 1 ) (n + 1 ) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full x_pre i (repeat_Z (49) (i)) )
  **  (CharArray.undef_seg x_pre i (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre <= i)) (PreH10 : (i <= n)) ,
  (CharArray.full x_pre (i + 1 ) (app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg x_pre (i + 1 ) (n + 1 ) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (b_pre <= i)) (PreH9 : (i <= n)) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full x_pre i (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre ))))) )
  **  (CharArray.undef_seg x_pre i (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (b_pre <= i)) (PreH9 : (i <= n)) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre i (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre ))))) )
  **  (CharArray.undef_seg x_pre i (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 <= n)) (PreH8 : ((n + 1 ) < INT_MAX)) (PreH9 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH10 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ ((n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 <= n)) (PreH8 : ((n + 1 ) < INT_MAX)) (PreH9 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH10 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (retval = y_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= n)) (PreH9 : ((n + 1 ) < INT_MAX)) (PreH10 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH11 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (k_pre = 0)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (CanonicalGambit a_pre b_pre k_pre )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre <> 0)) (PreH2 : (retval = y_pre)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (0 <= n)) (PreH10 : ((n + 1 ) < INT_MAX)) (PreH11 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH12 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_13 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (k_pre <> 0)) (PreH3 : (retval = y_pre)) (PreH4 : (n = (a_pre + b_pre ))) (PreH5 : (0 <= a_pre)) (PreH6 : (1 <= b_pre)) (PreH7 : (0 <= k_pre)) (PreH8 : (k_pre <= n)) (PreH9 : (n <= 200000)) (PreH10 : (0 <= n)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH13 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (b_pre >= 2)) (PreH2 : (a_pre <> 0)) (PreH3 : (k_pre <> 0)) (PreH4 : (retval = y_pre)) (PreH5 : (n = (a_pre + b_pre ))) (PreH6 : (0 <= a_pre)) (PreH7 : (1 <= b_pre)) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= n)) (PreH10 : (n <= 200000)) (PreH11 : (0 <= n)) (PreH12 : ((n + 1 ) < INT_MAX)) (PreH13 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH14 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 2 )) ”
.

Definition solver_safety_wit_15 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (b_pre >= 2)) (PreH2 : (a_pre <> 0)) (PreH3 : (k_pre <> 0)) (PreH4 : (retval = y_pre)) (PreH5 : (n = (a_pre + b_pre ))) (PreH6 : (0 <= a_pre)) (PreH7 : (1 <= b_pre)) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= n)) (PreH10 : (n <= 200000)) (PreH11 : (0 <= n)) (PreH12 : ((n + 1 ) < INT_MAX)) (PreH13 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH14 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_16 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 < k_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (k_pre > (n - 2 ))) (PreH9 : (GambitImpossible a_pre b_pre k_pre )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 < k_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (b_pre < 2)) (PreH9 : (GambitImpossible a_pre b_pre k_pre )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_18 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 < k_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (a_pre = 0)) (PreH9 : (GambitImpossible a_pre b_pre k_pre )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_19 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre <= a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((b_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_pre - 1 )) ”
.

Definition solver_safety_wit_20 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre <= a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre <= a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> (b_pre - 1 ))
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (((b_pre - 1 ) + k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_pre - 1 ) + k_pre )) ”
.

Definition solver_safety_wit_22 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre > a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre > a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_24 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre > a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |-> (n - 1 ))
  **  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (((n - 1 ) - k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n - 1 ) - k_pre )) ”
.

Definition solver_safety_wit_25 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= (b_pre - 1 ))) (PreH2 : ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre ))) (PreH3 : (((b_pre - 1 ) + k_pre ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre <= a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "j" ) )) # Int  |-> ((b_pre - 1 ) + k_pre ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_26 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= ((n - 1 ) - k_pre ))) (PreH2 : (((n - 1 ) - k_pre ) < (n - 1 ))) (PreH3 : ((n - 1 ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre > a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> ((n - 1 ) - k_pre ))
  **  ((( &( "j" ) )) # Int  |-> (n - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition solver_safety_wit_27 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= (b_pre - 1 ))) (PreH2 : ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre ))) (PreH3 : (((b_pre - 1 ) + k_pre ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre <= a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (replace_Znth ((b_pre - 1 )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "i" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "j" ) )) # Int  |-> ((b_pre - 1 ) + k_pre ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_28 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= ((n - 1 ) - k_pre ))) (PreH2 : (((n - 1 ) - k_pre ) < (n - 1 ))) (PreH3 : ((n - 1 ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre > a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (replace_Znth (((n - 1 ) - k_pre )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) )
  **  ((( &( "i" ) )) # Int  |-> ((n - 1 ) - k_pre ))
  **  ((( &( "j" ) )) # Int  |-> (n - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition solver_safety_wit_29 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (i: Z) (j: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 < k_pre)) (PreH8 : (0 < a_pre)) (PreH9 : (2 <= b_pre)) (PreH10 : (k_pre <= (n - 2 ))) (PreH11 : (1 <= i)) (PreH12 : (i < j)) (PreH13 : (j < n)) (PreH14 : ((j - i ) = k_pre)) (PreH15 : (k_pre > a_pre)) (PreH16 : (j = (n - 1 ))) (PreH17 : (i = (j - k_pre ))) (PreH18 : (CanonicalGambit a_pre b_pre k_pre )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth (j) (49) ((replace_Znth (i) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_30 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (i: Z) (j: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 < k_pre)) (PreH8 : (0 < a_pre)) (PreH9 : (2 <= b_pre)) (PreH10 : (k_pre <= (n - 2 ))) (PreH11 : (1 <= i)) (PreH12 : (i < j)) (PreH13 : (j < n)) (PreH14 : ((j - i ) = k_pre)) (PreH15 : (k_pre <= a_pre)) (PreH16 : (i = (b_pre - 1 ))) (PreH17 : (j = (i + k_pre ))) (PreH18 : (CanonicalGambit a_pre b_pre k_pre )) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth (j) (49) ((replace_Znth (i) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (1 <= b_pre)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= (a_pre + b_pre ))) (PreH5 : ((a_pre + b_pre ) <= 200000)) ,
  (CharArray.undef_full x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.undef_full y_pre ((a_pre + b_pre ) + 1 ) )
|--
  “ ((a_pre + b_pre ) = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= (a_pre + b_pre )) ” 
  &&  “ ((a_pre + b_pre ) <= 200000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= b_pre) ”
  &&  (CharArray.full x_pre 0 (repeat_Z (49) (0)) )
  **  (CharArray.undef_seg x_pre 0 ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.undef_full y_pre ((a_pre + b_pre ) + 1 ) )
) \/
(
forall (k_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (1 <= b_pre)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= (a_pre + b_pre ))) (PreH5 : ((a_pre + b_pre ) <= 200000)) ,
  TT && emp 
|--
  “ ((repeat_Z (49) (0)) = (@nil Z)) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= a_pre)) (PreH2 : (1 <= b_pre)) (PreH3 : (0 <= k_pre)) (PreH4 : (k_pre <= (a_pre + b_pre ))) (PreH5 : ((a_pre + b_pre ) <= 200000)) ,
  ((repeat_Z (49) (0)) = (@nil Z))
.

Definition solver_entail_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  (CharArray.full x_pre (i + 1 ) (app ((repeat_Z (49) (i))) ((cons (49) ((@nil Z))))) )
  **  (CharArray.undef_seg x_pre (i + 1 ) (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= b_pre) ”
  &&  (CharArray.full x_pre (i + 1 ) (repeat_Z (49) ((i + 1 ))) )
  **  (CharArray.undef_seg x_pre (i + 1 ) (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
) \/
(
forall (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  TT && emp 
|--
  “ ((app ((repeat_Z (49) (i))) ((cons (49) ((@nil Z))))) = (repeat_Z (49) ((i + 1 )))) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  ((app ((repeat_Z (49) (i))) ((cons (49) ((@nil Z))))) = (repeat_Z (49) ((i + 1 ))))
.

Definition solver_entail_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i >= b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  (CharArray.full x_pre i (repeat_Z (49) (i)) )
  **  (CharArray.undef_seg x_pre i (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (b_pre <= b_pre) ” 
  &&  “ (b_pre <= n) ”
  &&  (CharArray.full x_pre b_pre (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((b_pre - b_pre ))))) )
  **  (CharArray.undef_seg x_pre b_pre (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
) \/
(
forall (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i >= b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  (CharArray.full x_pre i (repeat_Z (49) (i)) )
|--
  (CharArray.full x_pre b_pre (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((b_pre - b_pre ))))) )
).

Definition solver_entail_wit_3_split_goal_spatial := 
forall (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i >= b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  (CharArray.full x_pre i (repeat_Z (49) (i)) )
|--
  (CharArray.full x_pre b_pre (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((b_pre - b_pre ))))) )
.

Definition solver_entail_wit_4 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre <= i)) (PreH10 : (i <= n)) ,
  (CharArray.full x_pre (i + 1 ) (app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (48) ((@nil Z))))) )
  **  (CharArray.undef_seg x_pre (i + 1 ) (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (b_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ”
  &&  (CharArray.full x_pre (i + 1 ) (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) (((i + 1 ) - b_pre ))))) )
  **  (CharArray.undef_seg x_pre (i + 1 ) (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
) \/
(
forall (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre <= i)) (PreH10 : (i <= n)) ,
  TT && emp 
|--
  “ ((app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (48) ((@nil Z))))) = (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) (((i + 1 ) - b_pre )))))) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre <= i)) (PreH10 : (i <= n)) ,
  ((app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (48) ((@nil Z))))) = (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) (((i + 1 ) - b_pre ))))))
.

Definition solver_entail_wit_5 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= i)) (PreH2 : (i >= n)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre <= i)) (PreH10 : (i <= n)) ,
  (CharArray.full x_pre (i + 1 ) (app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg x_pre (i + 1 ) (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
) \/
(
forall (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i >= n)) (PreH4 : (n = (a_pre + b_pre ))) (PreH5 : (0 <= a_pre)) (PreH6 : (1 <= b_pre)) (PreH7 : (0 <= k_pre)) (PreH8 : (k_pre <= n)) (PreH9 : (n <= 200000)) (PreH10 : (b_pre <= i)) (PreH11 : (i <= n)) ,
  (CharArray.full x_pre (i + 1 ) (app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (0) ((@nil Z))))) )
|--
  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = ((a_pre + b_pre ) + 1 )) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i >= n)) (PreH4 : (n = (a_pre + b_pre ))) (PreH5 : (0 <= a_pre)) (PreH6 : (1 <= b_pre)) (PreH7 : (0 <= k_pre)) (PreH8 : (k_pre <= n)) (PreH9 : (n <= 200000)) (PreH10 : (b_pre <= i)) (PreH11 : (i <= n)) ,
  (CharArray.full x_pre (i + 1 ) (app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (0) ((@nil Z))))) )
|--
  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = ((a_pre + b_pre ) + 1 )) ”
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i >= n)) (PreH4 : (n = (a_pre + b_pre ))) (PreH5 : (0 <= a_pre)) (PreH6 : (1 <= b_pre)) (PreH7 : (0 <= k_pre)) (PreH8 : (k_pre <= n)) (PreH9 : (n <= 200000)) (PreH10 : (b_pre <= i)) (PreH11 : (i <= n)) ,
  (CharArray.full x_pre (i + 1 ) (app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (0) ((@nil Z))))) )
|--
  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ”
.

Definition solver_entail_wit_5_split_goal_spatial := 
forall (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i >= n)) (PreH4 : (n = (a_pre + b_pre ))) (PreH5 : (0 <= a_pre)) (PreH6 : (1 <= b_pre)) (PreH7 : (0 <= k_pre)) (PreH8 : (k_pre <= n)) (PreH9 : (n <= 200000)) (PreH10 : (b_pre <= i)) (PreH11 : (i <= n)) ,
  (CharArray.full x_pre (i + 1 ) (app ((app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre )))))) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
.

Definition solver_entail_wit_6 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre = 0)) (PreH2 : (retval = y_pre)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (0 <= n)) (PreH10 : ((n + 1 ) < INT_MAX)) (PreH11 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH12 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (k_pre = 0) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (CanonicalGambit a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
) \/
(
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre = 0)) (PreH2 : (retval = y_pre)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (0 <= n)) (PreH10 : ((n + 1 ) < INT_MAX)) (PreH11 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH12 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  TT && emp 
|--
  “ (CanonicalGambit a_pre b_pre 0 ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre = 0)) (PreH2 : (retval = y_pre)) (PreH3 : (n = (a_pre + b_pre ))) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (0 <= n)) (PreH10 : ((n + 1 ) < INT_MAX)) (PreH11 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH12 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CanonicalGambit a_pre b_pre 0 )
.

Definition solver_entail_wit_7_1 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (b_pre < 2)) (PreH2 : (a_pre <> 0)) (PreH3 : (k_pre <> 0)) (PreH4 : (retval = y_pre)) (PreH5 : (n = (a_pre + b_pre ))) (PreH6 : (0 <= a_pre)) (PreH7 : (1 <= b_pre)) (PreH8 : (0 <= k_pre)) (PreH9 : (k_pre <= n)) (PreH10 : (n <= 200000)) (PreH11 : (0 <= n)) (PreH12 : ((n + 1 ) < INT_MAX)) (PreH13 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH14 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  (“ (n = (a_pre + b_pre )) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (k_pre > (n - 2 )) ” 
  &&  “ (GambitImpossible a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ))
  ||
  (“ (n = (a_pre + b_pre )) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (b_pre < 2) ” 
  &&  “ (GambitImpossible a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ))
.

Definition solver_entail_wit_7_2 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (a_pre = 0)) (PreH2 : (k_pre <> 0)) (PreH3 : (retval = y_pre)) (PreH4 : (n = (a_pre + b_pre ))) (PreH5 : (0 <= a_pre)) (PreH6 : (1 <= b_pre)) (PreH7 : (0 <= k_pre)) (PreH8 : (k_pre <= n)) (PreH9 : (n <= 200000)) (PreH10 : (0 <= n)) (PreH11 : ((n + 1 ) < INT_MAX)) (PreH12 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH13 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  (“ (n = (a_pre + b_pre )) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (k_pre > (n - 2 )) ” 
  &&  “ (GambitImpossible a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ))
  ||
  (“ (n = (a_pre + b_pre )) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (b_pre < 2) ” 
  &&  “ (GambitImpossible a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ))
  ||
  (“ (n = (a_pre + b_pre )) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (a_pre = 0) ” 
  &&  “ (GambitImpossible a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ))
.

Definition solver_entail_wit_7_3 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre > (n - 2 ))) (PreH2 : (b_pre >= 2)) (PreH3 : (a_pre <> 0)) (PreH4 : (k_pre <> 0)) (PreH5 : (retval = y_pre)) (PreH6 : (n = (a_pre + b_pre ))) (PreH7 : (0 <= a_pre)) (PreH8 : (1 <= b_pre)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= n)) (PreH11 : (n <= 200000)) (PreH12 : (0 <= n)) (PreH13 : ((n + 1 ) < INT_MAX)) (PreH14 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH15 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (k_pre > (n - 2 )) ” 
  &&  “ (GambitImpossible a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
) \/
(
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre > (n - 2 ))) (PreH2 : (b_pre >= 2)) (PreH3 : (a_pre <> 0)) (PreH4 : (k_pre <> 0)) (PreH5 : (retval = y_pre)) (PreH6 : (n = (a_pre + b_pre ))) (PreH7 : (0 <= a_pre)) (PreH8 : (1 <= b_pre)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= n)) (PreH11 : (n <= 200000)) (PreH12 : (0 <= n)) (PreH13 : ((n + 1 ) < INT_MAX)) (PreH14 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH15 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  TT && emp 
|--
  “ (GambitImpossible a_pre b_pre k_pre ) ”
  &&  emp
).

Definition solver_entail_wit_7_3_split_goal_1 := 
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre > (n - 2 ))) (PreH2 : (b_pre >= 2)) (PreH3 : (a_pre <> 0)) (PreH4 : (k_pre <> 0)) (PreH5 : (retval = y_pre)) (PreH6 : (n = (a_pre + b_pre ))) (PreH7 : (0 <= a_pre)) (PreH8 : (1 <= b_pre)) (PreH9 : (0 <= k_pre)) (PreH10 : (k_pre <= n)) (PreH11 : (n <= 200000)) (PreH12 : (0 <= n)) (PreH13 : ((n + 1 ) < INT_MAX)) (PreH14 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH15 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (GambitImpossible a_pre b_pre k_pre )
.

Definition solver_entail_wit_8_1 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre <= a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |-> ((b_pre - 1 ) + k_pre ))
  **  ((( &( "i" ) )) # Int  |-> (b_pre - 1 ))
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= (b_pre - 1 )) ” 
  &&  “ ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre )) ” 
  &&  “ (((b_pre - 1 ) + k_pre ) < n) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (b_pre >= INT_MIN) ” 
  &&  “ (a_pre >= INT_MIN) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (k_pre <= a_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (b_pre >= 2) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (k_pre <> 0) ” 
  &&  “ (retval = y_pre) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> (b_pre - 1 ))
  **  ((( &( "j" ) )) # Int  |-> ((b_pre - 1 ) + k_pre ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
.

Definition solver_entail_wit_8_2 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (k_pre > a_pre)) (PreH2 : (k_pre <= (n - 2 ))) (PreH3 : (b_pre >= 2)) (PreH4 : (a_pre <> 0)) (PreH5 : (k_pre <> 0)) (PreH6 : (retval = y_pre)) (PreH7 : (n = (a_pre + b_pre ))) (PreH8 : (0 <= a_pre)) (PreH9 : (1 <= b_pre)) (PreH10 : (0 <= k_pre)) (PreH11 : (k_pre <= n)) (PreH12 : (n <= 200000)) (PreH13 : (0 <= n)) (PreH14 : ((n + 1 ) < INT_MAX)) (PreH15 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH16 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "j" ) )) # Int  |-> (n - 1 ))
  **  ((( &( "i" ) )) # Int  |-> ((n - 1 ) - k_pre ))
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= ((n - 1 ) - k_pre )) ” 
  &&  “ (((n - 1 ) - k_pre ) < (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (b_pre >= INT_MIN) ” 
  &&  “ (a_pre >= INT_MIN) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (k_pre > a_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (b_pre >= 2) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (k_pre <> 0) ” 
  &&  “ (retval = y_pre) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  ((( &( "i" ) )) # Int  |-> ((n - 1 ) - k_pre ))
  **  ((( &( "j" ) )) # Int  |-> (n - 1 ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
.

Definition solver_entail_wit_9_1 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= (b_pre - 1 ))) (PreH2 : ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre ))) (PreH3 : (((b_pre - 1 ) + k_pre ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre <= a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (replace_Znth (((b_pre - 1 ) + k_pre )) (49) ((replace_Znth ((b_pre - 1 )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 < a_pre) ” 
  &&  “ (2 <= b_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (1 <= (b_pre - 1 )) ” 
  &&  “ ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre )) ” 
  &&  “ (((b_pre - 1 ) + k_pre ) < n) ” 
  &&  “ ((((b_pre - 1 ) + k_pre ) - (b_pre - 1 ) ) = k_pre) ” 
  &&  “ (k_pre <= a_pre) ” 
  &&  “ ((b_pre - 1 ) = (b_pre - 1 )) ” 
  &&  “ (((b_pre - 1 ) + k_pre ) = ((b_pre - 1 ) + k_pre )) ” 
  &&  “ (CanonicalGambit a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth (((b_pre - 1 ) + k_pre )) (49) ((replace_Znth ((b_pre - 1 )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
) \/
(
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= (b_pre - 1 ))) (PreH2 : ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre ))) (PreH3 : (((b_pre - 1 ) + k_pre ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre <= a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  TT && emp 
|--
  “ (CanonicalGambit a_pre b_pre k_pre ) ”
  &&  emp
).

Definition solver_entail_wit_9_1_split_goal_1 := 
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= (b_pre - 1 ))) (PreH2 : ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre ))) (PreH3 : (((b_pre - 1 ) + k_pre ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre <= a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CanonicalGambit a_pre b_pre k_pre )
.

Definition solver_entail_wit_9_2 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= ((n - 1 ) - k_pre ))) (PreH2 : (((n - 1 ) - k_pre ) < (n - 1 ))) (PreH3 : ((n - 1 ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre > a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (replace_Znth ((n - 1 )) (49) ((replace_Znth (((n - 1 ) - k_pre )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 < k_pre) ” 
  &&  “ (0 < a_pre) ” 
  &&  “ (2 <= b_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (1 <= ((n - 1 ) - k_pre )) ” 
  &&  “ (((n - 1 ) - k_pre ) < (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (((n - 1 ) - ((n - 1 ) - k_pre ) ) = k_pre) ” 
  &&  “ (k_pre > a_pre) ” 
  &&  “ ((n - 1 ) = (n - 1 )) ” 
  &&  “ (((n - 1 ) - k_pre ) = ((n - 1 ) - k_pre )) ” 
  &&  “ (CanonicalGambit a_pre b_pre k_pre ) ”
  &&  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth ((n - 1 )) (49) ((replace_Znth (((n - 1 ) - k_pre )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
) \/
(
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= ((n - 1 ) - k_pre ))) (PreH2 : (((n - 1 ) - k_pre ) < (n - 1 ))) (PreH3 : ((n - 1 ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre > a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  TT && emp 
|--
  “ (CanonicalGambit a_pre b_pre k_pre ) ”
  &&  emp
).

Definition solver_entail_wit_9_2_split_goal_1 := 
forall (y_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= ((n - 1 ) - k_pre ))) (PreH2 : (((n - 1 ) - k_pre ) < (n - 1 ))) (PreH3 : ((n - 1 ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre > a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CanonicalGambit a_pre b_pre k_pre )
.

Definition solver_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (i_2: Z) (j: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 < k_pre)) (PreH8 : (0 < a_pre)) (PreH9 : (2 <= b_pre)) (PreH10 : (k_pre <= (n - 2 ))) (PreH11 : (1 <= i_2)) (PreH12 : (i_2 < j)) (PreH13 : (j < n)) (PreH14 : ((j - i_2 ) = k_pre)) (PreH15 : (k_pre > a_pre)) (PreH16 : (j = (n - 1 ))) (PreH17 : (i_2 = (j - k_pre ))) (PreH18 : (CanonicalGambit a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth (j) (49) ((replace_Znth (i_2) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
|--
  EX (ybytes: (@list Z))  (xbytes: (@list Z))  (xs: (@list Z))  (ys: (@list Z))  (out: (@option ((@list Z) * (@list Z)))) ,
  “ (Spec a_pre b_pre k_pre out ) ” 
  &&  “ (out = (Some ((pair (xs) (ys))))) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (xs)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ys)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (xbytes)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ybytes)) = (a_pre + b_pre )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (a_pre + b_pre ))) -> (((Znth i xbytes 0) = ((Znth i xs 0) + 48 )) /\ ((Znth i ybytes 0) = ((Znth i ys 0) + 48 )))) ”
  &&  (CharArray.full x_pre ((a_pre + b_pre ) + 1 ) (app (xbytes) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full y_pre ((a_pre + b_pre ) + 1 ) (app (ybytes) ((cons (0) ((@nil Z))))) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (i_2: Z) (j: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 < k_pre)) (PreH9 : (0 < a_pre)) (PreH10 : (2 <= b_pre)) (PreH11 : (k_pre <= (n - 2 ))) (PreH12 : (1 <= i_2)) (PreH13 : (i_2 < j)) (PreH14 : (j < n)) (PreH15 : ((j - i_2 ) = k_pre)) (PreH16 : (k_pre > a_pre)) (PreH17 : (j = (n - 1 ))) (PreH18 : (i_2 = (j - k_pre ))) (PreH19 : (CanonicalGambit a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth (j) (49) ((replace_Znth (i_2) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
|--
  EX (ybytes: (@list Z))  (xbytes: (@list Z))  (xs: (@list Z))  (ys: (@list Z)) ,
  “ (Spec a_pre b_pre k_pre (Some ((pair (xs) (ys)))) ) ” 
  &&  “ ((Zlength (xs)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ys)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (xbytes)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ybytes)) = (a_pre + b_pre )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (a_pre + b_pre ))) -> (((Znth i xbytes 0) = ((Znth i xs 0) + 48 )) /\ ((Znth i ybytes 0) = ((Znth i ys 0) + 48 )))) ”
  &&  (CharArray.full x_pre ((a_pre + b_pre ) + 1 ) (app (xbytes) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full y_pre ((a_pre + b_pre ) + 1 ) (app (ybytes) ((cons (0) ((@nil Z))))) )
).

Definition solver_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (i_2: Z) (j: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 < k_pre)) (PreH8 : (0 < a_pre)) (PreH9 : (2 <= b_pre)) (PreH10 : (k_pre <= (n - 2 ))) (PreH11 : (1 <= i_2)) (PreH12 : (i_2 < j)) (PreH13 : (j < n)) (PreH14 : ((j - i_2 ) = k_pre)) (PreH15 : (k_pre <= a_pre)) (PreH16 : (i_2 = (b_pre - 1 ))) (PreH17 : (j = (i_2 + k_pre ))) (PreH18 : (CanonicalGambit a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth (j) (49) ((replace_Znth (i_2) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
|--
  EX (ybytes: (@list Z))  (xbytes: (@list Z))  (xs: (@list Z))  (ys: (@list Z))  (out: (@option ((@list Z) * (@list Z)))) ,
  “ (Spec a_pre b_pre k_pre out ) ” 
  &&  “ (out = (Some ((pair (xs) (ys))))) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (xs)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ys)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (xbytes)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ybytes)) = (a_pre + b_pre )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (a_pre + b_pre ))) -> (((Znth i xbytes 0) = ((Znth i xs 0) + 48 )) /\ ((Znth i ybytes 0) = ((Znth i ys 0) + 48 )))) ”
  &&  (CharArray.full x_pre ((a_pre + b_pre ) + 1 ) (app (xbytes) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full y_pre ((a_pre + b_pre ) + 1 ) (app (ybytes) ((cons (0) ((@nil Z))))) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (i_2: Z) (j: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 < k_pre)) (PreH9 : (0 < a_pre)) (PreH10 : (2 <= b_pre)) (PreH11 : (k_pre <= (n - 2 ))) (PreH12 : (1 <= i_2)) (PreH13 : (i_2 < j)) (PreH14 : (j < n)) (PreH15 : ((j - i_2 ) = k_pre)) (PreH16 : (k_pre <= a_pre)) (PreH17 : (i_2 = (b_pre - 1 ))) (PreH18 : (j = (i_2 + k_pre ))) (PreH19 : (CanonicalGambit a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (replace_Znth (j) (49) ((replace_Znth (i_2) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))))) )
|--
  EX (ybytes: (@list Z))  (xbytes: (@list Z))  (xs: (@list Z))  (ys: (@list Z)) ,
  “ (Spec a_pre b_pre k_pre (Some ((pair (xs) (ys)))) ) ” 
  &&  “ ((Zlength (xs)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ys)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (xbytes)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ybytes)) = (a_pre + b_pre )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (a_pre + b_pre ))) -> (((Znth i xbytes 0) = ((Znth i xs 0) + 48 )) /\ ((Znth i ybytes 0) = ((Znth i ys 0) + 48 )))) ”
  &&  (CharArray.full x_pre ((a_pre + b_pre ) + 1 ) (app (xbytes) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full y_pre ((a_pre + b_pre ) + 1 ) (app (ybytes) ((cons (0) ((@nil Z))))) )
).

Definition solver_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 < k_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (k_pre > (n - 2 ))) (PreH9 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  EX (out: (@option ((@list Z) * (@list Z)))) ,
  “ (Spec a_pre b_pre k_pre out ) ” 
  &&  “ (out = None) ” 
  &&  “ (0 = 0) ”
  &&  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (k_pre > (n - 2 ))) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (Spec a_pre b_pre k_pre None ) ”
  &&  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
).

Definition solver_return_wit_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (k_pre > (n - 2 ))) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (Spec a_pre b_pre k_pre None ) ”
.

Definition solver_return_wit_3_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (k_pre > (n - 2 ))) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
.

Definition solver_return_wit_4 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 < k_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (b_pre < 2)) (PreH9 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  EX (out: (@option ((@list Z) * (@list Z)))) ,
  “ (Spec a_pre b_pre k_pre out ) ” 
  &&  “ (out = None) ” 
  &&  “ (0 = 0) ”
  &&  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre < 2)) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (Spec a_pre b_pre k_pre None ) ”
  &&  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
).

Definition solver_return_wit_4_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre < 2)) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (Spec a_pre b_pre k_pre None ) ”
.

Definition solver_return_wit_4_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (b_pre < 2)) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
.

Definition solver_return_wit_5 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 < k_pre)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (a_pre = 0)) (PreH9 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  EX (out: (@option ((@list Z) * (@list Z)))) ,
  “ (Spec a_pre b_pre k_pre out ) ” 
  &&  “ (out = None) ” 
  &&  “ (0 = 0) ”
  &&  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (a_pre = 0)) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (Spec 0 b_pre k_pre None ) ”
  &&  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
).

Definition solver_return_wit_5_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (a_pre = 0)) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (Spec 0 b_pre k_pre None ) ”
.

Definition solver_return_wit_5_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 < k_pre)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (a_pre = 0)) (PreH10 : (GambitImpossible a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  (CharArray.full_shape x_pre ((a_pre + b_pre ) + 1 ) )
  **  (CharArray.full_shape y_pre ((a_pre + b_pre ) + 1 ) )
.

Definition solver_return_wit_6 := 
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (k_pre = 0)) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (CanonicalGambit a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  EX (ybytes: (@list Z))  (xbytes: (@list Z))  (xs: (@list Z))  (ys: (@list Z))  (out: (@option ((@list Z) * (@list Z)))) ,
  “ (Spec a_pre b_pre k_pre out ) ” 
  &&  “ (out = (Some ((pair (xs) (ys))))) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((Zlength (xs)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ys)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (xbytes)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ybytes)) = (a_pre + b_pre )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (a_pre + b_pre ))) -> (((Znth i xbytes 0) = ((Znth i xs 0) + 48 )) /\ ((Znth i ybytes 0) = ((Znth i ys 0) + 48 )))) ”
  &&  (CharArray.full x_pre ((a_pre + b_pre ) + 1 ) (app (xbytes) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full y_pre ((a_pre + b_pre ) + 1 ) (app (ybytes) ((cons (0) ((@nil Z))))) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (0 <= (n + 1 ))) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (k_pre = 0)) (PreH4 : (0 <= a_pre)) (PreH5 : (1 <= b_pre)) (PreH6 : (0 <= k_pre)) (PreH7 : (k_pre <= n)) (PreH8 : (n <= 200000)) (PreH9 : (CanonicalGambit a_pre b_pre k_pre )) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  EX (ybytes: (@list Z))  (xbytes: (@list Z))  (xs: (@list Z))  (ys: (@list Z)) ,
  “ (Spec a_pre b_pre k_pre (Some ((pair (xs) (ys)))) ) ” 
  &&  “ ((Zlength (xs)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ys)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (xbytes)) = (a_pre + b_pre )) ” 
  &&  “ ((Zlength (ybytes)) = (a_pre + b_pre )) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (a_pre + b_pre ))) -> (((Znth i xbytes 0) = ((Znth i xs 0) + 48 )) /\ ((Znth i ybytes 0) = ((Znth i ys 0) + 48 )))) ”
  &&  (CharArray.full x_pre ((a_pre + b_pre ) + 1 ) (app (xbytes) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full y_pre ((a_pre + b_pre ) + 1 ) (app (ybytes) ((cons (0) ((@nil Z))))) )
).

Definition solver_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < b_pre)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (0 <= i)) (PreH9 : (i <= b_pre)) ,
  (CharArray.full x_pre i (repeat_Z (49) (i)) )
  **  (CharArray.undef_seg x_pre i (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (i < b_pre) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= b_pre) ”
  &&  (((x_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i x_pre i i (n + 1 ) )
  **  (CharArray.full x_pre i (repeat_Z (49) (i)) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
.

Definition solver_partial_solve_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i < n)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (b_pre <= i)) (PreH9 : (i <= n)) ,
  (CharArray.full x_pre i (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre ))))) )
  **  (CharArray.undef_seg x_pre i (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (b_pre <= i) ” 
  &&  “ (i <= n) ”
  &&  (((x_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i x_pre i i (n + 1 ) )
  **  (CharArray.full x_pre i (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre ))))) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
.

Definition solver_partial_solve_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (n: Z) (PreH1 : (i >= n)) (PreH2 : (n = (a_pre + b_pre ))) (PreH3 : (0 <= a_pre)) (PreH4 : (1 <= b_pre)) (PreH5 : (0 <= k_pre)) (PreH6 : (k_pre <= n)) (PreH7 : (n <= 200000)) (PreH8 : (b_pre <= i)) (PreH9 : (i <= n)) ,
  (CharArray.full x_pre i (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre ))))) )
  **  (CharArray.undef_seg x_pre i (n + 1 ) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (0 <= i) ” 
  &&  “ (i >= n) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (b_pre <= i) ” 
  &&  “ (i <= n) ”
  &&  (((x_pre + (n * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i x_pre n i (n + 1 ) )
  **  (CharArray.full x_pre i (app ((repeat_Z (49) (b_pre))) ((repeat_Z (48) ((i - b_pre ))))) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
.

Definition solver_partial_solve_wit_4_pure := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 <= n)) (PreH8 : ((n + 1 ) < INT_MAX)) (PreH9 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH10 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ”
.

Definition solver_partial_solve_wit_4_aux := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (PreH1 : (n = (a_pre + b_pre ))) (PreH2 : (0 <= a_pre)) (PreH3 : (1 <= b_pre)) (PreH4 : (0 <= k_pre)) (PreH5 : (k_pre <= n)) (PreH6 : (n <= 200000)) (PreH7 : (0 <= n)) (PreH8 : ((n + 1 ) < INT_MAX)) (PreH9 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH10 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.undef_full y_pre (n + 1 ) )
|--
  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  (CharArray.undef_full y_pre (n + 1 ) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
.

Definition solver_partial_solve_wit_4 := solver_partial_solve_wit_4_pure -> solver_partial_solve_wit_4_aux.

Definition solver_partial_solve_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= (b_pre - 1 ))) (PreH2 : ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre ))) (PreH3 : (((b_pre - 1 ) + k_pre ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre <= a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (1 <= (b_pre - 1 )) ” 
  &&  “ ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre )) ” 
  &&  “ (((b_pre - 1 ) + k_pre ) < n) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (b_pre >= INT_MIN) ” 
  &&  “ (a_pre >= INT_MIN) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (k_pre <= a_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (b_pre >= 2) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (k_pre <> 0) ” 
  &&  “ (retval = y_pre) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  (((y_pre + ((b_pre - 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i y_pre (b_pre - 1 ) 0 (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
.

Definition solver_partial_solve_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= ((n - 1 ) - k_pre ))) (PreH2 : (((n - 1 ) - k_pre ) < (n - 1 ))) (PreH3 : ((n - 1 ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre > a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (1 <= ((n - 1 ) - k_pre )) ” 
  &&  “ (((n - 1 ) - k_pre ) < (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (b_pre >= INT_MIN) ” 
  &&  “ (a_pre >= INT_MIN) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (k_pre > a_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (b_pre >= 2) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (k_pre <> 0) ” 
  &&  “ (retval = y_pre) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  (((y_pre + (((n - 1 ) - k_pre ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i y_pre ((n - 1 ) - k_pre ) 0 (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
.

Definition solver_partial_solve_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= (b_pre - 1 ))) (PreH2 : ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre ))) (PreH3 : (((b_pre - 1 ) + k_pre ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre <= a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (replace_Znth ((b_pre - 1 )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (1 <= (b_pre - 1 )) ” 
  &&  “ ((b_pre - 1 ) < ((b_pre - 1 ) + k_pre )) ” 
  &&  “ (((b_pre - 1 ) + k_pre ) < n) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (b_pre >= INT_MIN) ” 
  &&  “ (a_pre >= INT_MIN) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (k_pre <= a_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (b_pre >= 2) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (k_pre <> 0) ” 
  &&  “ (retval = y_pre) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  (((y_pre + (((b_pre - 1 ) + k_pre ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i y_pre ((b_pre - 1 ) + k_pre ) 0 (n + 1 ) (replace_Znth ((b_pre - 1 )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
.

Definition solver_partial_solve_wit_8 := 
forall (y_pre: Z) (x_pre: Z) (k_pre: Z) (b_pre: Z) (a_pre: Z) (n: Z) (retval: Z) (PreH1 : (1 <= ((n - 1 ) - k_pre ))) (PreH2 : (((n - 1 ) - k_pre ) < (n - 1 ))) (PreH3 : ((n - 1 ) < n)) (PreH4 : (k_pre <= INT_MAX)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (a_pre <= INT_MAX)) (PreH7 : (k_pre >= INT_MIN)) (PreH8 : (b_pre >= INT_MIN)) (PreH9 : (a_pre >= INT_MIN)) (PreH10 : (0 <= (n + 1 ))) (PreH11 : (k_pre > a_pre)) (PreH12 : (k_pre <= (n - 2 ))) (PreH13 : (b_pre >= 2)) (PreH14 : (a_pre <> 0)) (PreH15 : (k_pre <> 0)) (PreH16 : (retval = y_pre)) (PreH17 : (n = (a_pre + b_pre ))) (PreH18 : (0 <= a_pre)) (PreH19 : (1 <= b_pre)) (PreH20 : (0 <= k_pre)) (PreH21 : (k_pre <= n)) (PreH22 : (n <= 200000)) (PreH23 : (0 <= n)) (PreH24 : ((n + 1 ) < INT_MAX)) (PreH25 : (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )) (PreH26 : ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 ))) ,
  (CharArray.full y_pre (n + 1 ) (replace_Znth (((n - 1 ) - k_pre )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
|--
  “ (1 <= ((n - 1 ) - k_pre )) ” 
  &&  “ (((n - 1 ) - k_pre ) < (n - 1 )) ” 
  &&  “ ((n - 1 ) < n) ” 
  &&  “ (k_pre <= INT_MAX) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (k_pre >= INT_MIN) ” 
  &&  “ (b_pre >= INT_MIN) ” 
  &&  “ (a_pre >= INT_MIN) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (k_pre > a_pre) ” 
  &&  “ (k_pre <= (n - 2 )) ” 
  &&  “ (b_pre >= 2) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (k_pre <> 0) ” 
  &&  “ (retval = y_pre) ” 
  &&  “ (n = (a_pre + b_pre )) ” 
  &&  “ (0 <= a_pre) ” 
  &&  “ (1 <= b_pre) ” 
  &&  “ (0 <= k_pre) ” 
  &&  “ (k_pre <= n) ” 
  &&  “ (n <= 200000) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((n + 1 ) < INT_MAX) ” 
  &&  “ (all_ascii (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) ) ” 
  &&  “ ((Zlength ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) = (n + 1 )) ”
  &&  (((y_pre + ((n - 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.missing_i y_pre (n - 1 ) 0 (n + 1 ) (replace_Znth (((n - 1 ) - k_pre )) (48) ((app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))))) )
  **  (CharArray.full x_pre (n + 1 ) (app ((repeat_Z (49) (b_pre))) ((app ((repeat_Z (48) (a_pre))) ((cons (0) ((@nil Z))))))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.
Axiom proof_of_solver_return_wit_5 : solver_return_wit_5.
Axiom proof_of_solver_return_wit_6 : solver_return_wit_6.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.

End VC_Correct.
