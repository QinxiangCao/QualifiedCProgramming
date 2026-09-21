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
Require Import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib.
Local Open Scope sac.

(*----- Function multipleKnapsack -----*)

Definition multipleKnapsack_safety_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "q_val" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_idx" ) ) 1001 )
  **  (IntArray.undef_full ( &( "old" ) ) 1001 )
  **  (IntArray.undef_full ( &( "dp" ) ) 1001 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "q_idx" ) ) 0 (j + 1 ) (app (qidx0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_6 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "q_val" ) ) 0 (j + 1 ) (app (qval0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 (j + 1 ) (app (qidx0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition multipleKnapsack_safety_wit_7 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_8 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_9 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) (replace_Znth (j) ((Znth j dp_l 0)) (old_l)) )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition multipleKnapsack_safety_wit_10 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  (IntArray.full counts_pre n_pre counts_l )
  **  ((( &( "cnt" ) )) # Int  |-> (Znth i counts_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth i values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth i weights_l 0))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_11 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (r > capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH29 : (Forall (Z.le (0)) old_l )) (PreH30 : (Forall (Z.ge (1000000)) old_l )) (PreH31 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ False ”
.

Definition multipleKnapsack_safety_wit_12 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH29 : (Forall (Z.le (0)) old_l )) (PreH30 : (Forall (Z.ge (1000000)) old_l )) (PreH31 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "head" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_13 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH29 : (Forall (Z.le (0)) old_l )) (PreH30 : (Forall (Z.ge (1000000)) old_l )) (PreH31 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "tail" ) )) # Int  |->_)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_14 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH29 : (Forall (Z.le (0)) old_l )) (PreH30 : (Forall (Z.ge (1000000)) old_l )) (PreH31 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Int  |-> 0)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multipleKnapsack_safety_wit_15 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth pos old_l 0) - (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos old_l 0) - (k * v ) )) ”
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth pos old_l 0) - (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth pos old_l 0) - (k * v ) )) ”
).

Definition multipleKnapsack_safety_wit_15_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth pos old_l 0) - (k * v ) ) <= INT_MAX) ”
.

Definition multipleKnapsack_safety_wit_15_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((INT_MIN) <= ((Znth pos old_l 0) - (k * v ) )) ”
.

Definition multipleKnapsack_safety_wit_16 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((k * v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * v )) ”
.

Definition multipleKnapsack_safety_wit_17 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((k - cnt ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - cnt )) ”
.

Definition multipleKnapsack_safety_wit_18 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth head qidx_l 0) < (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((head + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (head + 1 )) ”
.

Definition multipleKnapsack_safety_wit_19 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition multipleKnapsack_safety_wit_20 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition multipleKnapsack_safety_wit_21 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) <= current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition multipleKnapsack_safety_wit_22 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((tail + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail + 1 )) ”
.

Definition multipleKnapsack_safety_wit_23 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((tail + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail + 1 )) ”
.

Definition multipleKnapsack_safety_wit_24 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) ”
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) ”
).

Definition multipleKnapsack_safety_wit_24_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) ) <= INT_MAX) ”
.

Definition multipleKnapsack_safety_wit_24_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) ”
.

Definition multipleKnapsack_safety_wit_25 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((k * v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * v )) ”
.

Definition multipleKnapsack_safety_wit_26 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) ”
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) ”
).

Definition multipleKnapsack_safety_wit_26_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) ) <= INT_MAX) ”
.

Definition multipleKnapsack_safety_wit_26_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((INT_MIN) <= ((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) ”
.

Definition multipleKnapsack_safety_wit_27 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((k * v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k * v )) ”
.

Definition multipleKnapsack_safety_wit_28 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) (dp_l)) )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition multipleKnapsack_safety_wit_29 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) (dp_l)) )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "current" ) )) # Int  |-> current)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition multipleKnapsack_safety_wit_30 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) (dp_l)) )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((pos + w ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + w )) ”
.

Definition multipleKnapsack_safety_wit_31 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l)) 0) + (k * v ) )) (dp_l)) )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> (tail + 1 ))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((pos + w ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + w )) ”
.

Definition multipleKnapsack_safety_wit_32 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (pos > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "cnt" ) )) # Int  |-> cnt)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((r + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r + 1 )) ”
.

Definition multipleKnapsack_safety_wit_33 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (r >= w)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l 0))) (PreH16 : (v = (Znth i values_l 0))) (PreH17 : (cnt = (Znth i counts_l 0))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1 ))) (PreH20 : (0 <= v)) (PreH21 : (v <= 1000)) (PreH22 : (0 <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : (0 <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1 ))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH28 : (Forall (Z.le (0)) old_l )) (PreH29 : (Forall (Z.ge (1000000)) old_l )) (PreH30 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l dp_l r w v cnt capacity_pre )) (PreH32 : (Forall (Z.le (1)) weights_l )) (PreH33 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH34 : (Forall (Z.le (0)) values_l )) (PreH35 : (Forall (Z.ge (1000)) values_l )) (PreH36 : (Forall (Z.le (0)) counts_l )) (PreH37 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "counts" ) )) # Ptr  |-> counts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition multipleKnapsack_entail_wit_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.undef_full ( &( "q_val" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_idx" ) ) 1001 )
  **  (IntArray.undef_full ( &( "old" ) ) 1001 )
  **  (IntArray.undef_full ( &( "dp" ) ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
|--
  EX (qval0: (@list Z))  (qidx0: (@list Z))  (old0: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = 0) ” 
  &&  “ ((Zlength (old0)) = 0) ” 
  &&  “ ((Zlength (qidx0)) = 0) ” 
  &&  “ ((Zlength (qval0)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 0 dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) 0 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 0 old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) 0 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 0 qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) 0 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 0 qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) 0 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_1_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (eq (0)) (@nil Z) )
.

Definition multipleKnapsack_entail_wit_1_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition multipleKnapsack_entail_wit_1_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition multipleKnapsack_entail_wit_1_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition multipleKnapsack_entail_wit_1_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 1000)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : ((Zlength (counts_l)) = n_pre)) (PreH8 : (Forall (Z.le (1)) weights_l )) (PreH9 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (1000)) values_l )) (PreH12 : (Forall (Z.le (0)) counts_l )) (PreH13 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition multipleKnapsack_entail_wit_2 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0_2: (@list Z)) (qidx0_2: (@list Z)) (old0_2: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "q_val" ) ) 0 (j + 1 ) (app (qval0_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 (j + 1 ) (app (qidx0_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
|--
  EX (qval0: (@list Z))  (qidx0: (@list Z))  (old0: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (j + 1 )) ” 
  &&  “ ((Zlength (old0)) = (j + 1 )) ” 
  &&  “ ((Zlength (qidx0)) = (j + 1 )) ” 
  &&  “ ((Zlength (qval0)) = (j + 1 )) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 (j + 1 ) qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 (j + 1 ) qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (j + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0_2: (@list Z)) (qidx0_2: (@list Z)) (old0_2: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (app (dp_l_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (qval0_2) ((cons (0) ((@nil Z))))))) = (j + 1 )) ” 
  &&  “ ((Zlength ((app (qidx0_2) ((cons (0) ((@nil Z))))))) = (j + 1 )) ” 
  &&  “ ((Zlength ((app (old0_2) ((cons (0) ((@nil Z))))))) = (j + 1 )) ” 
  &&  “ ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) = (j + 1 )) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_2_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0_2: (@list Z)) (qidx0_2: (@list Z)) (old0_2: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (eq (0)) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
.

Definition multipleKnapsack_entail_wit_2_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0_2: (@list Z)) (qidx0_2: (@list Z)) (old0_2: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((app (qval0_2) ((cons (0) ((@nil Z))))))) = (j + 1 ))
.

Definition multipleKnapsack_entail_wit_2_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0_2: (@list Z)) (qidx0_2: (@list Z)) (old0_2: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((app (qidx0_2) ((cons (0) ((@nil Z))))))) = (j + 1 ))
.

Definition multipleKnapsack_entail_wit_2_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0_2: (@list Z)) (qidx0_2: (@list Z)) (old0_2: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((app (old0_2) ((cons (0) ((@nil Z))))))) = (j + 1 ))
.

Definition multipleKnapsack_entail_wit_2_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0_2: (@list Z)) (qidx0_2: (@list Z)) (old0_2: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0_2)) = j)) (PreH11 : ((Zlength (qidx0_2)) = j)) (PreH12 : ((Zlength (qval0_2)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) = (j + 1 ))
.

Definition multipleKnapsack_entail_wit_3 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l 0 capacity_pre dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "dp" ) ) 0 j dp_l_2 )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l 0 capacity_pre dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
).

Definition multipleKnapsack_entail_wit_4 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefixSemantics dp_l old_l 0 ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (MKCopyPrefixSemantics dp_l_2 old_l_2 0 ) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_4_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKCopyPrefixSemantics dp_l_2 old_l_2 0 )
.

Definition multipleKnapsack_entail_wit_5 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) (replace_Znth (j) ((Znth j dp_l_2 0)) (old_l_2)) )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefixSemantics dp_l old_l (j + 1 ) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (MKCopyPrefixSemantics dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 0)) (old_l_2)) (j + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (j) ((Znth j dp_l_2 0)) (old_l_2)))) = (capacity_pre + 1 )) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_5_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKCopyPrefixSemantics dp_l_2 (replace_Znth (j) ((Znth j dp_l_2 0)) (old_l_2)) (j + 1 ) )
.

Definition multipleKnapsack_entail_wit_5_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((replace_Znth (j) ((Znth j dp_l_2 0)) (old_l_2)))) = (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_6 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Znth i weights_l 0) = (Znth i weights_l 0)) ” 
  &&  “ ((Znth i values_l 0) = (Znth i values_l 0)) ” 
  &&  “ ((Znth i counts_l 0) = (Znth i counts_l 0)) ” 
  &&  “ (1 <= (Znth i weights_l 0)) ” 
  &&  “ ((Znth i weights_l 0) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= (Znth i values_l 0)) ” 
  &&  “ ((Znth i values_l 0) <= 1000) ” 
  &&  “ (0 <= (Znth i counts_l 0)) ” 
  &&  “ ((Znth i counts_l 0) <= capacity_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Znth i weights_l 0)) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResidueProgressSemantics old_l dp_l 0 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (MKItemResidueProgressSemantics old_l_2 dp_l_2 0 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l_2 ) ” 
  &&  “ (Forall (Z.le (0)) old_l_2 ) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (0 <= (Znth i weights_l 0)) ” 
  &&  “ ((Znth i counts_l 0) <= capacity_pre) ” 
  &&  “ (0 <= (Znth i counts_l 0)) ” 
  &&  “ ((Znth i values_l 0) <= 1000) ” 
  &&  “ (0 <= (Znth i values_l 0)) ” 
  &&  “ ((Znth i weights_l 0) <= (capacity_pre + 1 )) ” 
  &&  “ (1 <= (Znth i weights_l 0)) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_6_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKItemResidueProgressSemantics old_l_2 dp_l_2 0 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre )
.

Definition multipleKnapsack_entail_wit_6_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_6_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge (1000000)) old_l_2 )
.

Definition multipleKnapsack_entail_wit_6_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le (0)) old_l_2 )
.

Definition multipleKnapsack_entail_wit_6_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )
.

Definition multipleKnapsack_entail_wit_6_split_goal_6 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (0 <= (Znth i weights_l 0))
.

Definition multipleKnapsack_entail_wit_6_split_goal_7 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Znth i counts_l 0) <= capacity_pre)
.

Definition multipleKnapsack_entail_wit_6_split_goal_8 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (0 <= (Znth i counts_l 0))
.

Definition multipleKnapsack_entail_wit_6_split_goal_9 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Znth i values_l 0) <= 1000)
.

Definition multipleKnapsack_entail_wit_6_split_goal_10 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (0 <= (Znth i values_l 0))
.

Definition multipleKnapsack_entail_wit_6_split_goal_11 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Znth i weights_l 0) <= (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_6_split_goal_12 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l_2 )) (PreH18 : (MKCopyPrefixSemantics dp_l_2 old_l_2 j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (1 <= (Znth i weights_l 0))
.

Definition multipleKnapsack_entail_wit_7 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH29 : (Forall (Z.le (0)) old_l_2 )) (PreH30 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH31 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (r = (r + (0 * w ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r <= (capacity_pre + w )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt 0 capacity_pre ) ” 
  &&  “ (MKQueueResultSemantics old_l qidx_l qval_l 0 0 r w v cnt 0 capacity_pre ) ” 
  &&  “ (Forall (Z.le ((-((0 - 1 ) * v )))) (sublist (0) (0) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - ((0 - 1 ) * v ) ))) (sublist (0) (0) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH29 : (Forall (Z.le (0)) old_l_2 )) (PreH30 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH31 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (Z.ge ((1000000 - ((0 - 1 ) * v ) ))) (sublist (0) (0) (qval_l_2)) ) ” 
  &&  “ (Forall (Z.le ((-((0 - 1 ) * v )))) (sublist (0) (0) (qval_l_2)) ) ” 
  &&  “ (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 0 0 r w v cnt 0 capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt 0 capacity_pre ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_7_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH29 : (Forall (Z.le (0)) old_l_2 )) (PreH30 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH31 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge ((1000000 - ((0 - 1 ) * v ) ))) (sublist (0) (0) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_7_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH29 : (Forall (Z.le (0)) old_l_2 )) (PreH30 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH31 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le ((-((0 - 1 ) * v )))) (sublist (0) (0) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_7_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH29 : (Forall (Z.le (0)) old_l_2 )) (PreH30 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH31 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 0 0 r w v cnt 0 capacity_pre )
.

Definition multipleKnapsack_entail_wit_7_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH29 : (Forall (Z.le (0)) old_l_2 )) (PreH30 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH31 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt 0 capacity_pre )
.

Definition multipleKnapsack_entail_wit_7_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r <= capacity_pre)) (PreH2 : (r < w)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (w = (Znth i weights_l 0))) (PreH17 : (v = (Znth i values_l 0))) (PreH18 : (cnt = (Znth i counts_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 1000)) (PreH23 : (0 <= cnt)) (PreH24 : (cnt <= capacity_pre)) (PreH25 : (0 <= r)) (PreH26 : (r <= w)) (PreH27 : (r <= (capacity_pre + 1 ))) (PreH28 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH29 : (Forall (Z.le (0)) old_l_2 )) (PreH30 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH31 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH32 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH35 : (Forall (Z.le (0)) values_l )) (PreH36 : (Forall (Z.ge (1000)) values_l )) (PreH37 : (Forall (Z.le (0)) counts_l )) (PreH38 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_8 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l_2: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l_2)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (((Znth pos old_l 0) - (k * v ) ) = ((Znth pos old_l_2 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ (((Znth pos old_l 0) - (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= (((Znth pos old_l 0) - (k * v ) ) + (k * v ) )) ” 
  &&  “ ((((Znth pos old_l 0) - (k * v ) ) + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 ) ” 
  &&  “ (Forall (Z.le (0)) old_l_2 ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l_2 ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l_2 dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropSemantics old_l_2 qidx_l qval_l head tail r w v cnt k ) ” 
  &&  “ (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (MKQueueDropSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ ((((Znth (r + (k * w ) ) old_l 0) - (k * v ) ) + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= (((Znth (r + (k * w ) ) old_l 0) - (k * v ) ) + (k * v ) )) ” 
  &&  “ (((Znth (r + (k * w ) ) old_l 0) - (k * v ) ) <= 1000000) ” 
  &&  “ ((-1000000) <= ((Znth (r + (k * w ) ) old_l 0) - (k * v ) )) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_8_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueueDropSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k )
.

Definition multipleKnapsack_entail_wit_8_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_8_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((((Znth (r + (k * w ) ) old_l 0) - (k * v ) ) + (k * v ) ) <= 1000000)
.

Definition multipleKnapsack_entail_wit_8_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (0 <= (((Znth (r + (k * w ) ) old_l 0) - (k * v ) ) + (k * v ) ))
.

Definition multipleKnapsack_entail_wit_8_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (((Znth (r + (k * w ) ) old_l 0) - (k * v ) ) <= 1000000)
.

Definition multipleKnapsack_entail_wit_8_split_goal_6 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((-1000000) <= ((Znth (r + (k * w ) ) old_l 0) - (k * v ) ))
.

Definition multipleKnapsack_entail_wit_9 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) < (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= (head + 1 )) ” 
  &&  “ ((head + 1 ) <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropSemantics old_l qidx_l qval_l (head + 1 ) tail r w v cnt k ) ” 
  &&  “ (Forall (Z.le ((-((k - 1 ) * v )))) (sublist ((head + 1 )) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist ((head + 1 )) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) < (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist ((head + 1 )) (tail) (qval_l_2)) ) ” 
  &&  “ (Forall (Z.le ((-((k - 1 ) * v )))) (sublist ((head + 1 )) (tail) (qval_l_2)) ) ” 
  &&  “ (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 (head + 1 ) tail r w v cnt k ) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_9_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) < (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist ((head + 1 )) (tail) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_9_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) < (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le ((-((k - 1 ) * v )))) (sublist ((head + 1 )) (tail) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_9_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) < (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 (head + 1 ) tail r w v cnt k )
.

Definition multipleKnapsack_entail_wit_10_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) ) ” 
  &&  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_10_1_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_10_1_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_10_1_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )
.

Definition multipleKnapsack_entail_wit_10_1_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_10_2 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) >= (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) >= (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) ) ” 
  &&  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_10_2_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) >= (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_10_2_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) >= (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_10_2_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) >= (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )
.

Definition multipleKnapsack_entail_wit_10_2_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth head qidx_l_2 0) >= (k - cnt ))) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k )) (PreH48 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_11 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) <= current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= (tail - 1 )) ” 
  &&  “ ((tail - 1 ) <= k) ” 
  &&  “ ((tail - 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head (tail - 1 ) r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) ((tail - 1 )) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) ((tail - 1 )) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) <= current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) ((tail - 1 )) (qval_l_2)) ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) ((tail - 1 )) (qval_l_2)) ) ” 
  &&  “ (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head (tail - 1 ) r w v cnt k current ) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_11_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) <= current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) ((tail - 1 )) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_11_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) <= current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le ((-(k * v )))) (sublist (head) ((tail - 1 )) (qval_l_2)) )
.

Definition multipleKnapsack_entail_wit_11_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) <= current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head (tail - 1 ) r w v cnt k current )
.

Definition multipleKnapsack_entail_wit_12_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)) )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l_2)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l_2)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ ((pos + w ) = (r + ((k + 1 ) * w ) )) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= (pos + w )) ” 
  &&  “ ((pos + w ) <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= (tail + 1 )) ” 
  &&  “ ((tail + 1 ) <= (k + 1 )) ” 
  &&  “ ((tail + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKQueueResultSemantics old_l qidx_l qval_l head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (Forall (Z.le ((-(((k + 1 ) - 1 ) * v )))) (sublist (head) ((tail + 1 )) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (((k + 1 ) - 1 ) * v ) ))) (sublist (head) ((tail + 1 )) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (Z.ge ((1000000 - (((k + 1 ) - 1 ) * v ) ))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) ) ” 
  &&  “ (Forall (Z.le ((-(((k + 1 ) - 1 ) * v )))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) ) ” 
  &&  “ (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (((r + (k * w ) ) + w ) = (r + ((k + 1 ) * w ) )) ” 
  &&  “ ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength ((replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)))) = (capacity_pre + 1 )) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_12_1_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge ((1000000 - (((k + 1 ) - 1 ) * v ) ))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) )
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le ((-(((k + 1 ) - 1 ) * v )))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) )
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre )
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)) r w v cnt (k + 1 ) capacity_pre )
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_6 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (((r + (k * w ) ) + w ) = (r + ((k + 1 ) * w ) ))
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_7 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_8 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_12_1_split_goal_9 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH42 : (Forall (Z.le (0)) old_l_2 )) (PreH43 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH44 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)))) = (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_12_2 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) (replace_Znth (pos) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)) )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l_2)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l_2)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ ((pos + w ) = (r + ((k + 1 ) * w ) )) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= (pos + w )) ” 
  &&  “ ((pos + w ) <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= (tail + 1 )) ” 
  &&  “ ((tail + 1 ) <= (k + 1 )) ” 
  &&  “ ((tail + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKQueueResultSemantics old_l qidx_l qval_l head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (Forall (Z.le ((-(((k + 1 ) - 1 ) * v )))) (sublist (head) ((tail + 1 )) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (((k + 1 ) - 1 ) * v ) ))) (sublist (head) ((tail + 1 )) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (Forall (Z.ge ((1000000 - (((k + 1 ) - 1 ) * v ) ))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) ) ” 
  &&  “ (Forall (Z.le ((-(((k + 1 ) - 1 ) * v )))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) ) ” 
  &&  “ (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)) r w v cnt (k + 1 ) capacity_pre ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (((r + (k * w ) ) + w ) = (r + ((k + 1 ) * w ) )) ” 
  &&  “ ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength ((replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)))) = (capacity_pre + 1 )) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_12_2_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.ge ((1000000 - (((k + 1 ) - 1 ) * v ) ))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) )
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (Forall (Z.le ((-(((k + 1 ) - 1 ) * v )))) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (current) (qval_l_2)))) )
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKQueueResultSemantics old_l_2 (replace_Znth (tail) (k) (qidx_l_2)) (replace_Znth (tail) (current) (qval_l_2)) head (tail + 1 ) r w v cnt (k + 1 ) capacity_pre )
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKItemResiduePrefixSemantics old_l_2 (replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)) r w v cnt (k + 1 ) capacity_pre )
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_6 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (((r + (k * w ) ) + w ) = (r + ((k + 1 ) * w ) ))
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_7 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((replace_Znth (tail) (current) (qval_l_2)))) = (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_8 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((replace_Znth (tail) (k) (qidx_l_2)))) = (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_12_2_split_goal_9 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l_2 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l_2 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH43 : (Forall (Z.le (0)) old_l_2 )) (PreH44 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH45 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  ((Zlength ((replace_Znth ((r + (k * w ) )) (((Znth head (replace_Znth (tail) (current) (qval_l_2)) 0) + (k * v ) )) (dp_l_2)))) = (capacity_pre + 1 ))
.

Definition multipleKnapsack_entail_wit_13 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH37 : (Forall (Z.le (0)) old_l_2 )) (PreH38 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (0 <= (r + 1 )) ” 
  &&  “ ((r + 1 ) <= w) ” 
  &&  “ ((r + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResidueProgressSemantics old_l dp_l (r + 1 ) w v cnt capacity_pre ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH37 : (Forall (Z.le (0)) old_l_2 )) (PreH38 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1 ) w v cnt capacity_pre ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_13_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH37 : (Forall (Z.le (0)) old_l_2 )) (PreH38 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKItemResidueProgressSemantics old_l_2 dp_l_2 (r + 1 ) w v cnt capacity_pre )
.

Definition multipleKnapsack_entail_wit_13_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (pos > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH37 : (Forall (Z.le (0)) old_l_2 )) (PreH38 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH39 : forall (p_2: Z) , forall (a_2: Z) , ((((0 <= p_2) /\ (p_2 <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p_2 a_2 )) -> ((0 <= a_2) /\ (a_2 <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l_2)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l_2)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))
.

Definition multipleKnapsack_entail_wit_14 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r >= w)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l 0))) (PreH16 : (v = (Znth i values_l 0))) (PreH17 : (cnt = (Znth i counts_l 0))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1 ))) (PreH20 : (0 <= v)) (PreH21 : (v <= 1000)) (PreH22 : (0 <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : (0 <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1 ))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH28 : (Forall (Z.le (0)) old_l_2 )) (PreH29 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH30 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH32 : (Forall (Z.le (1)) weights_l )) (PreH33 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH34 : (Forall (Z.le (0)) values_l )) (PreH35 : (Forall (Z.ge (1000)) values_l )) (PreH36 : (Forall (Z.le (0)) counts_l )) (PreH37 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l_2 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l_2 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l_2 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  EX (qval_l: (@list Z))  (qidx_l: (@list Z))  (old_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l (i + 1 ) capacity_pre dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r >= w)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l 0))) (PreH16 : (v = (Znth i values_l 0))) (PreH17 : (cnt = (Znth i counts_l 0))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1 ))) (PreH20 : (0 <= v)) (PreH21 : (v <= 1000)) (PreH22 : (0 <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : (0 <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1 ))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH28 : (Forall (Z.le (0)) old_l_2 )) (PreH29 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH30 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH32 : (Forall (Z.le (1)) weights_l )) (PreH33 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH34 : (Forall (Z.le (0)) values_l )) (PreH35 : (Forall (Z.ge (1000)) values_l )) (PreH36 : (Forall (Z.le (0)) counts_l )) (PreH37 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  TT && emp 
|--
  “ (MKDPTableSemantics weights_l values_l counts_l (i + 1 ) capacity_pre dp_l_2 ) ”
  &&  emp
).

Definition multipleKnapsack_entail_wit_14_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (r: Z) (cnt: Z) (v: Z) (w: Z) (i: Z) (qval_l_2: (@list Z)) (qidx_l_2: (@list Z)) (old_l_2: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (r >= w)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l_2)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l_2)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l_2)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (w = (Znth i weights_l 0))) (PreH16 : (v = (Znth i values_l 0))) (PreH17 : (cnt = (Znth i counts_l 0))) (PreH18 : (1 <= w)) (PreH19 : (w <= (capacity_pre + 1 ))) (PreH20 : (0 <= v)) (PreH21 : (v <= 1000)) (PreH22 : (0 <= cnt)) (PreH23 : (cnt <= capacity_pre)) (PreH24 : (0 <= r)) (PreH25 : (r <= w)) (PreH26 : (r <= (capacity_pre + 1 ))) (PreH27 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 )) (PreH28 : (Forall (Z.le (0)) old_l_2 )) (PreH29 : (Forall (Z.ge (1000000)) old_l_2 )) (PreH30 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l_2 w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH31 : (MKItemResidueProgressSemantics old_l_2 dp_l_2 r w v cnt capacity_pre )) (PreH32 : (Forall (Z.le (1)) weights_l )) (PreH33 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH34 : (Forall (Z.le (0)) values_l )) (PreH35 : (Forall (Z.ge (1000)) values_l )) (PreH36 : (Forall (Z.le (0)) counts_l )) (PreH37 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (MKDPTableSemantics weights_l values_l counts_l (i + 1 ) capacity_pre dp_l_2 )
.

Definition multipleKnapsack_entail_wit_15 := 
(
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l 0) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_full ( &( "dp" ) ) 1001 )
  **  (IntArray.undef_full ( &( "old" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_idx" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_val" ) ) 1001 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l 0) ) ”
  &&  (IntArray.undef_full ( &( "dp" ) ) 1001 )
  **  (IntArray.undef_full ( &( "old" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_idx" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_val" ) ) 1001 )
).

Definition multipleKnapsack_entail_wit_15_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre (Znth capacity_pre dp_l 0) ) ”
.

Definition multipleKnapsack_entail_wit_15_split_goal_spatial := 
forall (capacity_pre: Z) (n_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  (IntArray.undef_full ( &( "dp" ) ) 1001 )
  **  (IntArray.undef_full ( &( "old" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_idx" ) ) 1001 )
  **  (IntArray.undef_full ( &( "q_val" ) ) 1001 )
.

Definition multipleKnapsack_return_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (answer: Z) (PreH1 : (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre answer )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
|--
  “ (MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre answer ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
.

Definition multipleKnapsack_partial_solve_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) j 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ ((Zlength (old0)) = j) ” 
  &&  “ ((Zlength (qidx0)) = j) ” 
  &&  “ ((Zlength (qval0)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 j dp_l )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
.

Definition multipleKnapsack_partial_solve_wit_2 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.undef_seg ( &( "old" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ ((Zlength (old0)) = j) ” 
  &&  “ ((Zlength (qidx0)) = j) ” 
  &&  “ ((Zlength (qval0)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "old" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "old" ) ) 0 j old0 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
.

Definition multipleKnapsack_partial_solve_wit_3 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) j 1001 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ ((Zlength (old0)) = j) ” 
  &&  “ ((Zlength (qidx0)) = j) ” 
  &&  “ ((Zlength (qval0)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_idx" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 j qidx0 )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
.

Definition multipleKnapsack_partial_solve_wit_4 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (qval0: (@list Z)) (qidx0: (@list Z)) (old0: (@list Z)) (j: Z) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = j)) (PreH10 : ((Zlength (old0)) = j)) (PreH11 : ((Zlength (qidx0)) = j)) (PreH12 : ((Zlength (qval0)) = j)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (Forall (eq (0)) dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.seg ( &( "q_idx" ) ) 0 (j + 1 ) (app (qidx0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) j 1001 )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = j) ” 
  &&  “ ((Zlength (old0)) = j) ” 
  &&  “ ((Zlength (qidx0)) = j) ” 
  &&  “ ((Zlength (qval0)) = j) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_val" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "q_val" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "q_idx" ) ) 0 (j + 1 ) (app (qidx0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "old" ) ) 0 (j + 1 ) (app (old0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "old" ) ) (j + 1 ) 1001 )
  **  (IntArray.seg ( &( "dp" ) ) 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (j + 1 ) 1001 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.seg ( &( "q_val" ) ) 0 j qval0 )
.

Definition multipleKnapsack_partial_solve_wit_5 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefixSemantics dp_l old_l j ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "dp" ) ) + (j * sizeof(INT)))) # Int  |-> (Znth j dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) j 0 (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_6 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (j <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (j <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefixSemantics dp_l old_l j ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "old" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "old" ) ) j 0 (capacity_pre + 1 ) old_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_7 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefixSemantics dp_l old_l j ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((weights_pre + (i * sizeof(INT)))) # Int  |-> (Znth i weights_l 0))
  **  (IntArray.missing_i weights_pre i 0 n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_8 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefixSemantics dp_l old_l j ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((values_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values_l 0))
  **  (IntArray.missing_i values_pre i 0 n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_9 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (j: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (j > capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= j)) (PreH16 : (j <= (capacity_pre + 1 ))) (PreH17 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH18 : (MKCopyPrefixSemantics dp_l old_l j )) (PreH19 : (Forall (Z.le (1)) weights_l )) (PreH20 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH21 : (Forall (Z.le (0)) values_l )) (PreH22 : (Forall (Z.ge (1000)) values_l )) (PreH23 : (Forall (Z.le (0)) counts_l )) (PreH24 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (j > capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (MKCopyPrefixSemantics dp_l old_l j ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((counts_pre + (i * sizeof(INT)))) # Int  |-> (Znth i counts_l 0))
  **  (IntArray.missing_i counts_pre i 0 n_pre counts_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_10 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (pos <= capacity_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= (capacity_pre + 1 ))) (PreH30 : (0 <= pos)) (PreH31 : (pos <= (capacity_pre + w ))) (PreH32 : (0 <= head)) (PreH33 : (head <= tail)) (PreH34 : (tail <= k)) (PreH35 : (tail <= (capacity_pre + 1 ))) (PreH36 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH37 : (Forall (Z.le (0)) old_l )) (PreH38 : (Forall (Z.ge (1000000)) old_l )) (PreH39 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH40 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH41 : (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre )) (PreH42 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH43 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH44 : (Forall (Z.le (1)) weights_l )) (PreH45 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH46 : (Forall (Z.le (0)) values_l )) (PreH47 : (Forall (Z.ge (1000)) values_l )) (PreH48 : (Forall (Z.le (0)) counts_l )) (PreH49 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (pos <= capacity_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= (capacity_pre + w )) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueResultSemantics old_l qidx_l qval_l head tail r w v cnt k capacity_pre ) ” 
  &&  “ (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "old" ) ) + (pos * sizeof(INT)))) # Int  |-> (Znth pos old_l 0))
  **  (IntArray.missing_i ( &( "old" ) ) pos 0 (capacity_pre + 1 ) old_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_11 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k )) (PreH47 : (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueueDropSemantics old_l qidx_l qval_l head tail r w v cnt k ) ” 
  &&  “ (Forall (Z.le ((-((k - 1 ) * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - ((k - 1 ) * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_idx" ) ) + (head * sizeof(INT)))) # Int  |-> (Znth head qidx_l 0))
  **  (IntArray.missing_i ( &( "q_idx" ) ) head 0 (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_12 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_val" ) ) + ((tail - 1 ) * sizeof(INT)))) # Int  |-> (Znth (tail - 1 ) qval_l 0))
  **  (IntArray.missing_i ( &( "q_val" ) ) (tail - 1 ) 0 (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_13 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_idx" ) ) + (tail * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "q_idx" ) ) tail 0 (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_14 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_idx" ) ) + (tail * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "q_idx" ) ) tail 0 (capacity_pre + 1 ) qidx_l )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_15 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_val" ) ) + (tail * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "q_val" ) ) tail 0 (capacity_pre + 1 ) qval_l )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_16 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_val" ) ) + (tail * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "q_val" ) ) tail 0 (capacity_pre + 1 ) qval_l )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_17 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_val" ) ) + (head * sizeof(INT)))) # Int  |-> (Znth head (replace_Znth (tail) (current) (qval_l)) 0))
  **  (IntArray.missing_i ( &( "q_val" ) ) head 0 (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_18 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i < n_pre)) (PreH15 : (0 <= r)) (PreH16 : (r < w)) (PreH17 : (r <= capacity_pre)) (PreH18 : (w = (Znth i weights_l 0))) (PreH19 : (v = (Znth i values_l 0))) (PreH20 : (cnt = (Znth i counts_l 0))) (PreH21 : (1 <= w)) (PreH22 : (w <= (capacity_pre + 1 ))) (PreH23 : (0 <= v)) (PreH24 : (v <= 1000)) (PreH25 : (0 <= cnt)) (PreH26 : (cnt <= capacity_pre)) (PreH27 : (pos = (r + (k * w ) ))) (PreH28 : (0 <= k)) (PreH29 : (k <= capacity_pre)) (PreH30 : (0 <= pos)) (PreH31 : (pos <= capacity_pre)) (PreH32 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH33 : ((-1000000) <= current)) (PreH34 : (current <= 1000000)) (PreH35 : (0 <= (current + (k * v ) ))) (PreH36 : ((current + (k * v ) ) <= 1000000)) (PreH37 : (0 <= head)) (PreH38 : (head <= tail)) (PreH39 : (tail <= k)) (PreH40 : (tail <= (capacity_pre + 1 ))) (PreH41 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH42 : (Forall (Z.le (0)) old_l )) (PreH43 : (Forall (Z.ge (1000000)) old_l )) (PreH44 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH45 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH46 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH47 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH48 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.le (1)) weights_l )) (PreH50 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH51 : (Forall (Z.le (0)) values_l )) (PreH52 : (Forall (Z.ge (1000)) values_l )) (PreH53 : (Forall (Z.le (0)) counts_l )) (PreH54 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (head >= tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "dp" ) ) + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "dp" ) ) pos 0 (capacity_pre + 1 ) dp_l )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_19 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "q_val" ) ) + (head * sizeof(INT)))) # Int  |-> (Znth head (replace_Znth (tail) (current) (qval_l)) 0))
  **  (IntArray.missing_i ( &( "q_val" ) ) head 0 (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_20 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (tail: Z) (head: Z) (current: Z) (k: Z) (pos: Z) (cnt: Z) (v: Z) (w: Z) (r: Z) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : ((Znth (tail - 1 ) qval_l 0) > current)) (PreH2 : (head < tail)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 1000)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (values_l)) = n_pre)) (PreH9 : ((Zlength (counts_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH13 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH14 : (0 <= i)) (PreH15 : (i < n_pre)) (PreH16 : (0 <= r)) (PreH17 : (r < w)) (PreH18 : (r <= capacity_pre)) (PreH19 : (w = (Znth i weights_l 0))) (PreH20 : (v = (Znth i values_l 0))) (PreH21 : (cnt = (Znth i counts_l 0))) (PreH22 : (1 <= w)) (PreH23 : (w <= (capacity_pre + 1 ))) (PreH24 : (0 <= v)) (PreH25 : (v <= 1000)) (PreH26 : (0 <= cnt)) (PreH27 : (cnt <= capacity_pre)) (PreH28 : (pos = (r + (k * w ) ))) (PreH29 : (0 <= k)) (PreH30 : (k <= capacity_pre)) (PreH31 : (0 <= pos)) (PreH32 : (pos <= capacity_pre)) (PreH33 : (current = ((Znth pos old_l 0) - (k * v ) ))) (PreH34 : ((-1000000) <= current)) (PreH35 : (current <= 1000000)) (PreH36 : (0 <= (current + (k * v ) ))) (PreH37 : ((current + (k * v ) ) <= 1000000)) (PreH38 : (0 <= head)) (PreH39 : (head <= tail)) (PreH40 : (tail <= k)) (PreH41 : (tail <= (capacity_pre + 1 ))) (PreH42 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l )) (PreH43 : (Forall (Z.le (0)) old_l )) (PreH44 : (Forall (Z.ge (1000000)) old_l )) (PreH45 : forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000)))) (PreH46 : (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre )) (PreH47 : (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current )) (PreH48 : (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) )) (PreH49 : (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) )) (PreH50 : (Forall (Z.le (1)) weights_l )) (PreH51 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH52 : (Forall (Z.le (0)) values_l )) (PreH53 : (Forall (Z.ge (1000)) values_l )) (PreH54 : (Forall (Z.le (0)) counts_l )) (PreH55 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ ((Znth (tail - 1 ) qval_l 0) > current) ” 
  &&  “ (head < tail) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= r) ” 
  &&  “ (r < w) ” 
  &&  “ (r <= capacity_pre) ” 
  &&  “ (w = (Znth i weights_l 0)) ” 
  &&  “ (v = (Znth i values_l 0)) ” 
  &&  “ (cnt = (Znth i counts_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 1000) ” 
  &&  “ (0 <= cnt) ” 
  &&  “ (cnt <= capacity_pre) ” 
  &&  “ (pos = (r + (k * w ) )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= capacity_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= capacity_pre) ” 
  &&  “ (current = ((Znth pos old_l 0) - (k * v ) )) ” 
  &&  “ ((-1000000) <= current) ” 
  &&  “ (current <= 1000000) ” 
  &&  “ (0 <= (current + (k * v ) )) ” 
  &&  “ ((current + (k * v ) ) <= 1000000) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= k) ” 
  &&  “ (tail <= (capacity_pre + 1 )) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l ) ” 
  &&  “ (Forall (Z.le (0)) old_l ) ” 
  &&  “ (Forall (Z.ge (1000000)) old_l ) ” 
  &&  “ forall (p: Z) , forall (a: Z) , ((((0 <= p) /\ (p <= capacity_pre)) /\ (MKTransitionSemantics old_l w v cnt capacity_pre p a )) -> ((0 <= a) /\ (a <= 1000000))) ” 
  &&  “ (MKItemResiduePrefixSemantics old_l dp_l r w v cnt k capacity_pre ) ” 
  &&  “ (MKQueuePendingSemantics old_l qidx_l qval_l head tail r w v cnt k current ) ” 
  &&  “ (Forall (Z.le ((-(k * v )))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.ge ((1000000 - (k * v ) ))) (sublist (head) (tail) (qval_l)) ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "dp" ) ) + (pos * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "dp" ) ) pos 0 (capacity_pre + 1 ) dp_l )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (current) (qval_l)) )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) (replace_Znth (tail) (k) (qidx_l)) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Definition multipleKnapsack_partial_solve_wit_21 := 
forall (capacity_pre: Z) (n_pre: Z) (counts_pre: Z) (values_pre: Z) (weights_pre: Z) (counts_l: (@list Z)) (values_l: (@list Z)) (weights_l: (@list Z)) (i: Z) (qval_l: (@list Z)) (qidx_l: (@list Z)) (old_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 1000)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (values_l)) = n_pre)) (PreH8 : ((Zlength (counts_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = (capacity_pre + 1 ))) (PreH10 : ((Zlength (old_l)) = (capacity_pre + 1 ))) (PreH11 : ((Zlength (qidx_l)) = (capacity_pre + 1 ))) (PreH12 : ((Zlength (qval_l)) = (capacity_pre + 1 ))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l )) (PreH16 : (Forall (Z.le (1)) weights_l )) (PreH17 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH18 : (Forall (Z.le (0)) values_l )) (PreH19 : (Forall (Z.ge (1000)) values_l )) (PreH20 : (Forall (Z.le (0)) counts_l )) (PreH21 : (Forall (Z.ge (capacity_pre)) counts_l )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.full ( &( "dp" ) ) (capacity_pre + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
|--
  “ (i >= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 1000) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ ((Zlength (counts_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (old_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qidx_l)) = (capacity_pre + 1 )) ” 
  &&  “ ((Zlength (qval_l)) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (MKDPTableSemantics weights_l values_l counts_l i capacity_pre dp_l ) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.ge ((capacity_pre + 1 ))) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (1000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) counts_l ) ” 
  &&  “ (Forall (Z.ge (capacity_pre)) counts_l ) ”
  &&  (((( &( "dp" ) ) + (capacity_pre * sizeof(INT)))) # Int  |-> (Znth capacity_pre dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) capacity_pre 0 (capacity_pre + 1 ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full counts_pre n_pre counts_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "old" ) ) (capacity_pre + 1 ) old_l )
  **  (IntArray.undef_seg ( &( "old" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_idx" ) ) (capacity_pre + 1 ) qidx_l )
  **  (IntArray.undef_seg ( &( "q_idx" ) ) (capacity_pre + 1 ) 1001 )
  **  (IntArray.full ( &( "q_val" ) ) (capacity_pre + 1 ) qval_l )
  **  (IntArray.undef_seg ( &( "q_val" ) ) (capacity_pre + 1 ) 1001 )
.

Module Type VC_Correct.


Axiom proof_of_multipleKnapsack_safety_wit_1 : multipleKnapsack_safety_wit_1.
Axiom proof_of_multipleKnapsack_safety_wit_2 : multipleKnapsack_safety_wit_2.
Axiom proof_of_multipleKnapsack_safety_wit_3 : multipleKnapsack_safety_wit_3.
Axiom proof_of_multipleKnapsack_safety_wit_4 : multipleKnapsack_safety_wit_4.
Axiom proof_of_multipleKnapsack_safety_wit_5 : multipleKnapsack_safety_wit_5.
Axiom proof_of_multipleKnapsack_safety_wit_6 : multipleKnapsack_safety_wit_6.
Axiom proof_of_multipleKnapsack_safety_wit_7 : multipleKnapsack_safety_wit_7.
Axiom proof_of_multipleKnapsack_safety_wit_8 : multipleKnapsack_safety_wit_8.
Axiom proof_of_multipleKnapsack_safety_wit_9 : multipleKnapsack_safety_wit_9.
Axiom proof_of_multipleKnapsack_safety_wit_10 : multipleKnapsack_safety_wit_10.
Axiom proof_of_multipleKnapsack_safety_wit_11 : multipleKnapsack_safety_wit_11.
Axiom proof_of_multipleKnapsack_safety_wit_12 : multipleKnapsack_safety_wit_12.
Axiom proof_of_multipleKnapsack_safety_wit_13 : multipleKnapsack_safety_wit_13.
Axiom proof_of_multipleKnapsack_safety_wit_14 : multipleKnapsack_safety_wit_14.
Axiom proof_of_multipleKnapsack_safety_wit_15 : multipleKnapsack_safety_wit_15.
Axiom proof_of_multipleKnapsack_safety_wit_16 : multipleKnapsack_safety_wit_16.
Axiom proof_of_multipleKnapsack_safety_wit_17 : multipleKnapsack_safety_wit_17.
Axiom proof_of_multipleKnapsack_safety_wit_18 : multipleKnapsack_safety_wit_18.
Axiom proof_of_multipleKnapsack_safety_wit_19 : multipleKnapsack_safety_wit_19.
Axiom proof_of_multipleKnapsack_safety_wit_20 : multipleKnapsack_safety_wit_20.
Axiom proof_of_multipleKnapsack_safety_wit_21 : multipleKnapsack_safety_wit_21.
Axiom proof_of_multipleKnapsack_safety_wit_22 : multipleKnapsack_safety_wit_22.
Axiom proof_of_multipleKnapsack_safety_wit_23 : multipleKnapsack_safety_wit_23.
Axiom proof_of_multipleKnapsack_safety_wit_24 : multipleKnapsack_safety_wit_24.
Axiom proof_of_multipleKnapsack_safety_wit_25 : multipleKnapsack_safety_wit_25.
Axiom proof_of_multipleKnapsack_safety_wit_26 : multipleKnapsack_safety_wit_26.
Axiom proof_of_multipleKnapsack_safety_wit_27 : multipleKnapsack_safety_wit_27.
Axiom proof_of_multipleKnapsack_safety_wit_28 : multipleKnapsack_safety_wit_28.
Axiom proof_of_multipleKnapsack_safety_wit_29 : multipleKnapsack_safety_wit_29.
Axiom proof_of_multipleKnapsack_safety_wit_30 : multipleKnapsack_safety_wit_30.
Axiom proof_of_multipleKnapsack_safety_wit_31 : multipleKnapsack_safety_wit_31.
Axiom proof_of_multipleKnapsack_safety_wit_32 : multipleKnapsack_safety_wit_32.
Axiom proof_of_multipleKnapsack_safety_wit_33 : multipleKnapsack_safety_wit_33.
Axiom proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1.
Axiom proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2.
Axiom proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3.
Axiom proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4.
Axiom proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5.
Axiom proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6.
Axiom proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7.
Axiom proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8.
Axiom proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9.
Axiom proof_of_multipleKnapsack_entail_wit_10_1 : multipleKnapsack_entail_wit_10_1.
Axiom proof_of_multipleKnapsack_entail_wit_10_2 : multipleKnapsack_entail_wit_10_2.
Axiom proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11.
Axiom proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1.
Axiom proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2.
Axiom proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13.
Axiom proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14.
Axiom proof_of_multipleKnapsack_entail_wit_15 : multipleKnapsack_entail_wit_15.
Axiom proof_of_multipleKnapsack_return_wit_1 : multipleKnapsack_return_wit_1.
Axiom proof_of_multipleKnapsack_partial_solve_wit_1 : multipleKnapsack_partial_solve_wit_1.
Axiom proof_of_multipleKnapsack_partial_solve_wit_2 : multipleKnapsack_partial_solve_wit_2.
Axiom proof_of_multipleKnapsack_partial_solve_wit_3 : multipleKnapsack_partial_solve_wit_3.
Axiom proof_of_multipleKnapsack_partial_solve_wit_4 : multipleKnapsack_partial_solve_wit_4.
Axiom proof_of_multipleKnapsack_partial_solve_wit_5 : multipleKnapsack_partial_solve_wit_5.
Axiom proof_of_multipleKnapsack_partial_solve_wit_6 : multipleKnapsack_partial_solve_wit_6.
Axiom proof_of_multipleKnapsack_partial_solve_wit_7 : multipleKnapsack_partial_solve_wit_7.
Axiom proof_of_multipleKnapsack_partial_solve_wit_8 : multipleKnapsack_partial_solve_wit_8.
Axiom proof_of_multipleKnapsack_partial_solve_wit_9 : multipleKnapsack_partial_solve_wit_9.
Axiom proof_of_multipleKnapsack_partial_solve_wit_10 : multipleKnapsack_partial_solve_wit_10.
Axiom proof_of_multipleKnapsack_partial_solve_wit_11 : multipleKnapsack_partial_solve_wit_11.
Axiom proof_of_multipleKnapsack_partial_solve_wit_12 : multipleKnapsack_partial_solve_wit_12.
Axiom proof_of_multipleKnapsack_partial_solve_wit_13 : multipleKnapsack_partial_solve_wit_13.
Axiom proof_of_multipleKnapsack_partial_solve_wit_14 : multipleKnapsack_partial_solve_wit_14.
Axiom proof_of_multipleKnapsack_partial_solve_wit_15 : multipleKnapsack_partial_solve_wit_15.
Axiom proof_of_multipleKnapsack_partial_solve_wit_16 : multipleKnapsack_partial_solve_wit_16.
Axiom proof_of_multipleKnapsack_partial_solve_wit_17 : multipleKnapsack_partial_solve_wit_17.
Axiom proof_of_multipleKnapsack_partial_solve_wit_18 : multipleKnapsack_partial_solve_wit_18.
Axiom proof_of_multipleKnapsack_partial_solve_wit_19 : multipleKnapsack_partial_solve_wit_19.
Axiom proof_of_multipleKnapsack_partial_solve_wit_20 : multipleKnapsack_partial_solve_wit_20.
Axiom proof_of_multipleKnapsack_partial_solve_wit_21 : multipleKnapsack_partial_solve_wit_21.

End VC_Correct.
