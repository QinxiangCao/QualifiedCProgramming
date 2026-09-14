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
Require Import SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib.
Local Open Scope sac.

(*----- Function lcs_n -----*)

Definition lcs_n_safety_wit_1 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stride" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition lcs_n_safety_wit_2 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stride" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_3 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stride" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lcs_n_safety_wit_4 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition lcs_n_safety_wit_5 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lcs_n_safety_wit_6 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth ((stride * i )) ((Some (0))) (mixed_table)) )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition lcs_n_safety_wit_7 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth ((stride * i )) ((Some (0))) (mixed_table)) )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_8 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_9 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (0 <= j)) (PreH2 : (j < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1 ))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lcs_n_safety_wit_10 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (0 <= j)) (PreH2 : (j < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1 ))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) ,
  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth (j) ((Some (0))) (mixed_table)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition lcs_n_safety_wit_11 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (0 <= j)) (PreH2 : (j < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1 ))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) ,
  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth (j) ((Some (0))) (mixed_table)) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_12 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_13 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table table_l n_pre i )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_14 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition lcs_n_safety_wit_15 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition lcs_n_safety_wit_16 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_17 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_18 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (((stride * i ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + j )) ”
.

Definition lcs_n_safety_wit_19 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition lcs_n_safety_wit_20 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l_2 n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) + 1 )) ”
.

Definition lcs_n_safety_wit_21 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (((stride * (i - 1 ) ) + (j - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * (i - 1 ) ) + (j - 1 ) )) ”
.

Definition lcs_n_safety_wit_22 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition lcs_n_safety_wit_23 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((stride * (i - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * (i - 1 ) )) ”
.

Definition lcs_n_safety_wit_24 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition lcs_n_safety_wit_25 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_26 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_27 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_28 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (((stride * (i - 1 ) ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * (i - 1 ) ) + j )) ”
.

Definition lcs_n_safety_wit_29 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((stride * (i - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * (i - 1 ) )) ”
.

Definition lcs_n_safety_wit_30 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition lcs_n_safety_wit_31 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_32 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (((stride * i ) + (j - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + (j - 1 ) )) ”
.

Definition lcs_n_safety_wit_33 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition lcs_n_safety_wit_34 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition lcs_n_safety_wit_35 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_36 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
|--
  “ (((stride * i ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + j )) ”
.

Definition lcs_n_safety_wit_37 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition lcs_n_safety_wit_38 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
|--
  “ (((stride * i ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + j )) ”
.

Definition lcs_n_safety_wit_39 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition lcs_n_safety_wit_40 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (i: Z) (j: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1 ))) (PreH11 : ((j + 1 ) <= (n_pre + 1 ))) (PreH12 : (0 <= ((stride * i ) + (j + 1 ) ))) (PreH13 : (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition lcs_n_safety_wit_41 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (i: Z) (j: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1 ))) (PreH11 : ((j + 1 ) <= (n_pre + 1 ))) (PreH12 : (0 <= ((stride * i ) + (j + 1 ) ))) (PreH13 : (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_42 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition lcs_n_safety_wit_43 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lcs_n_safety_wit_44 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH2 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride = (n_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) ,
  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (((stride * n_pre ) + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * n_pre ) + n_pre )) ”
.

Definition lcs_n_safety_wit_45 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH2 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride = (n_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) ,
  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ ((stride * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * n_pre )) ”
.

Definition lcs_n_entail_wit_1 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((n_pre + 1 ) * 0 )) ” 
  &&  “ (((n_pre + 1 ) * 0 ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNColumnProgress mixed_table table_l n_pre 0 ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
) \/
(
forall (table_pre: Z) (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (IntArray.undef_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((n_pre + 1 ) * 0 )) ” 
  &&  “ (((n_pre + 1 ) * 0 ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNColumnProgress mixed_table table_l n_pre 0 ) ”
  &&  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
).

Definition lcs_n_entail_wit_2 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (0 <= (stride * i )) ” 
  &&  “ ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= (stride * i )) ” 
  &&  “ ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNColumnProgress mixed_table table_l n_pre i ) ”
  &&  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (0 <= (stride * i ))) (PreH16 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  TT && emp 
|--
  “ (((n_pre + 1 ) * i ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition lcs_n_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (0 <= (stride * i ))) (PreH16 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  (((n_pre + 1 ) * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition lcs_n_entail_wit_3 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) ,
  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth ((stride * i )) ((Some (0))) (mixed_table_2)) )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= (stride * (i + 1 ) )) ” 
  &&  “ ((stride * (i + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNColumnProgress mixed_table table_l n_pre (i + 1 ) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= (((Zlength (xs)) + 1 ) * (i + 1 ) )) ” 
  &&  “ ((((Zlength (xs)) + 1 ) * (i + 1 ) ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNColumnProgress (replace_Znth ((((Zlength (xs)) + 1 ) * i )) ((Some (0))) (mixed_table_2)) table_l (Zlength (xs)) (i + 1 ) ) ”
  &&  emp
).

Definition lcs_n_entail_wit_4 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (LCSNBoundaryProgress mixed_table table_l n_pre 1 ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (LCSNBoundaryProgress mixed_table_2 table_l (Zlength (xs)) 1 ) ”
  &&  emp
).

Definition lcs_n_entail_wit_5 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (0 <= j) ” 
  &&  “ (j < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (stride <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (stride >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (LCSNBoundaryProgress mixed_table table_l n_pre j ) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
.

Definition lcs_n_entail_wit_6 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (0 <= j)) (PreH2 : (j < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1 ))) (PreH15 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) ,
  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth (j) ((Some (0))) (mixed_table_2)) )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (LCSNBoundaryProgress mixed_table table_l n_pre (j + 1 ) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (0 <= j)) (PreH2 : (j < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1 ))) (PreH15 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (LCSNBoundaryProgress (replace_Znth (j) ((Some (0))) (mixed_table_2)) table_l (Zlength (xs)) (j + 1 ) ) ”
  &&  emp
).

Definition lcs_n_entail_wit_7 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (stride * 1 )) ” 
  &&  “ ((stride * 1 ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre 1 ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= (((Zlength (xs)) + 1 ) * 1 )) ” 
  &&  “ ((((Zlength (xs)) + 1 ) * 1 ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) 1 ) ”
  &&  emp
).

Definition lcs_n_entail_wit_8 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + 1 )) ” 
  &&  “ (((stride * i ) + 1 ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i 1 ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= ((((Zlength (xs)) + 1 ) * i ) + 1 )) ” 
  &&  “ (((((Zlength (xs)) + 1 ) * i ) + 1 ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l (Zlength (xs)) i 1 ) ”
  &&  emp
).

Definition lcs_n_entail_wit_9 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  TT && emp 
|--
  “ ((((n_pre + 1 ) * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((((n_pre + 1 ) * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition lcs_n_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((((n_pre + 1 ) * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition lcs_n_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition lcs_n_entail_wit_9_split_goal_3 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  ((((n_pre + 1 ) * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition lcs_n_entail_wit_10_1 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_3: (@list (@option Z))) (table_l_3: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_3) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (IntArray.undef_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) + 1 ))
  **  (((table_pre + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_3)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + (j + 1 ) )) ” 
  &&  “ (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
) \/
(
forall (table_pre: Z) (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_3: (@list (@option Z))) (table_l_3: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) <= INT_MAX)) (PreH2 : (((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) + 1 ) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) >= INT_MIN)) (PreH4 : (((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) + 1 ) >= INT_MIN)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j )) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_3) (None)) = None)) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)))))) (PreH12 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)))) (PreH13 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) <= n_pre)) (PreH14 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (0 <= (j - 1 ))) (PreH18 : ((j - 1 ) < n_pre)) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH22 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH24 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH26 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre >= INT_MIN)) (PreH29 : (j <= n_pre)) (PreH30 : (stride = (n_pre + 1 ))) (PreH31 : (0 <= n_pre)) (PreH32 : (n_pre <= 1000)) (PreH33 : ((Zlength (xs)) = n_pre)) (PreH34 : ((Zlength (ys)) = n_pre)) (PreH35 : (1 <= i)) (PreH36 : (i <= n_pre)) (PreH37 : (1 <= j)) (PreH38 : (j <= (n_pre + 1 ))) (PreH39 : (0 <= ((stride * i ) + j ))) (PreH40 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)) + 1 ))
  **  (((table_pre + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_3) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_3)) )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + (j + 1 ) )) ” 
  &&  “ (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) ) ”
  &&  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
).

Definition lcs_n_entail_wit_10_2 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_3: (@list (@option Z))) (table_l_3: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_3) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (IntArray.undef_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_3)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + (j + 1 ) )) ” 
  &&  “ (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
) \/
(
forall (table_pre: Z) (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_3: (@list (@option Z))) (table_l_3: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j )) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_3) (None)) = None)) (PreH12 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))))) (PreH13 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))))) (PreH14 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (0 <= (j - 1 ))) (PreH18 : ((j - 1 ) < n_pre)) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH22 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH24 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH26 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre >= INT_MIN)) (PreH29 : (j <= n_pre)) (PreH30 : (stride = (n_pre + 1 ))) (PreH31 : (0 <= n_pre)) (PreH32 : (n_pre <= 1000)) (PreH33 : ((Zlength (xs)) = n_pre)) (PreH34 : ((Zlength (ys)) = n_pre)) (PreH35 : (1 <= i)) (PreH36 : (i <= n_pre)) (PreH37 : (1 <= j)) (PreH38 : (j <= (n_pre + 1 ))) (PreH39 : (0 <= ((stride * i ) + j ))) (PreH40 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_3)) )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + (j + 1 ) )) ” 
  &&  “ (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) ) ”
  &&  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
).

Definition lcs_n_entail_wit_10_3 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_3: (@list (@option Z))) (table_l_3: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_3) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (IntArray.undef_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
  **  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_3)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + (j + 1 ) )) ” 
  &&  “ (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
) \/
(
forall (table_pre: Z) (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_3: (@list (@option Z))) (table_l_3: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_3 table_l_3 n_pre i j )) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_3) (None)) = None)) (PreH12 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))))) (PreH13 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))))) (PreH14 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (0 <= (j - 1 ))) (PreH18 : ((j - 1 ) < n_pre)) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH22 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH24 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH26 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (n_pre >= INT_MIN)) (PreH29 : (j <= n_pre)) (PreH30 : (stride = (n_pre + 1 ))) (PreH31 : (0 <= n_pre)) (PreH32 : (n_pre <= 1000)) (PreH33 : ((Zlength (xs)) = n_pre)) (PreH34 : ((Zlength (ys)) = n_pre)) (PreH35 : (1 <= i)) (PreH36 : (i <= n_pre)) (PreH37 : (1 <= j)) (PreH38 : (j <= (n_pre + 1 ))) (PreH39 : (0 <= ((stride * i ) + j ))) (PreH40 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
  **  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_3) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_3) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_3)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_3)) )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + (j + 1 ) )) ” 
  &&  “ (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) ) ”
  &&  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
).

Definition lcs_n_entail_wit_11 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (stride: Z) (i: Z) (j: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1 ))) (PreH11 : ((j + 1 ) <= (n_pre + 1 ))) (PreH12 : (0 <= ((stride * i ) + (j + 1 ) ))) (PreH13 : (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i (j + 1 ) )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + (j + 1 ) )) ” 
  &&  “ (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
.

Definition lcs_n_entail_wit_12 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= (stride * (i + 1 ) )) ” 
  &&  “ ((stride * (i + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (i + 1 ) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= (((Zlength (xs)) + 1 ) * (i + 1 ) )) ” 
  &&  “ ((((Zlength (xs)) + 1 ) * (i + 1 ) ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) (i + 1 ) ) ”
  &&  emp
).

Definition lcs_n_entail_wit_13 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (LCSNTableResult xs ys n_pre table_l ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
) \/
(
forall (table_pre: Z) (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) ,
  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (LCSNTableResult xs ys n_pre table_l ) ”
  &&  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
).

Definition lcs_n_entail_wit_14 := 
(
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : (LCSNTableResult xs ys n_pre table_l )) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (0 <= ((stride * n_pre ) + n_pre )) ” 
  &&  “ (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (LCSNTableResult xs ys n_pre table_l ) ”
  &&  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (stride >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (stride = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (xs)) = n_pre)) (PreH9 : ((Zlength (ys)) = n_pre)) (PreH10 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH11 : (LCSNTableResult xs ys n_pre table_l )) ,
  TT && emp 
|--
  “ ((((n_pre + 1 ) * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition lcs_n_entail_wit_14_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (stride >= INT_MIN)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (stride = (n_pre + 1 ))) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (xs)) = n_pre)) (PreH9 : ((Zlength (ys)) = n_pre)) (PreH10 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH11 : (LCSNTableResult xs ys n_pre table_l )) ,
  ((((n_pre + 1 ) * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition lcs_n_return_wit_1 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l_2: (@list Z)) (stride: Z) (PreH1 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH2 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride = (n_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l_2 n_pre (n_pre + 1 ) )) (PreH9 : (LCSNTableResult xs ys n_pre table_l_2 )) ,
  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l_2 )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
|--
  EX (table_l: (@list Z)) ,
  “ (LCSNTableResult xs ys n_pre table_l ) ” 
  &&  “ ((Znth ((stride * n_pre ) + n_pre ) table_l_2 0) = (Znth ((((n_pre + 1 ) * n_pre ) + n_pre )) (table_l) (0))) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
.

Definition lcs_n_partial_solve_wit_1 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (0 <= (stride * i )) ” 
  &&  “ ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (0 <= (stride * i )) ” 
  &&  “ ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNColumnProgress mixed_table table_l n_pre i ) ”
  &&  (((table_pre + ((stride * i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i table_pre (stride * i ) 0 ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
.

Definition lcs_n_partial_solve_wit_2 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (0 <= j)) (PreH2 : (j < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (j <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= (n_pre + 1 ))) (PreH15 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (0 <= j) ” 
  &&  “ (j < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (stride <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (stride >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (LCSNBoundaryProgress mixed_table table_l n_pre j ) ”
  &&  (((table_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i table_pre j 0 ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
.

Definition lcs_n_partial_solve_wit_3 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((x_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) xs 0))
  **  (IntArray.missing_i x_pre (i - 1 ) 0 n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
.

Definition lcs_n_partial_solve_wit_4 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((y_pre + ((j - 1 ) * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) ys 0))
  **  (IntArray.missing_i y_pre (j - 1 ) 0 n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
.

Definition lcs_n_partial_solve_wit_5_pure := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
.

Definition lcs_n_partial_solve_wit_5_aux := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_5 := lcs_n_partial_solve_wit_5_pure -> lcs_n_partial_solve_wit_5_aux.

Definition lcs_n_partial_solve_wit_6 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0))))) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre) ” 
  &&  “ ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((table_pre + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_7 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH8 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH10 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0))))) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre) ” 
  &&  “ ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i table_pre ((stride * i ) + j ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((table_pre + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_8_pure := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "table" ) )) # Ptr  |-> table_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
.

Definition lcs_n_partial_solve_wit_8_aux := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (IntArray.mixed_full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_8 := lcs_n_partial_solve_wit_8_pure -> lcs_n_partial_solve_wit_8_aux.

Definition lcs_n_partial_solve_wit_9 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0))))) ” 
  &&  “ ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_10 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH7 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH9 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (0 <= (j - 1 ))) (PreH13 : ((j - 1 ) < n_pre)) (PreH14 : (0 <= ((stride * i ) + j ))) (PreH15 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH17 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH19 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH21 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (n_pre >= INT_MIN)) (PreH24 : (j <= n_pre)) (PreH25 : (stride = (n_pre + 1 ))) (PreH26 : (0 <= n_pre)) (PreH27 : (n_pre <= 1000)) (PreH28 : ((Zlength (xs)) = n_pre)) (PreH29 : ((Zlength (ys)) = n_pre)) (PreH30 : (1 <= i)) (PreH31 : (i <= n_pre)) (PreH32 : (1 <= j)) (PreH33 : (j <= (n_pre + 1 ))) (PreH34 : (0 <= ((stride * i ) + j ))) (PreH35 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH36 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (((table_pre + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0))))) ” 
  &&  “ ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_11 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
|--
  “ ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0))))) ” 
  &&  “ ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i table_pre ((stride * i ) + j ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_12 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH8 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH10 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH11 : (0 <= (i - 1 ))) (PreH12 : ((i - 1 ) < n_pre)) (PreH13 : (0 <= (j - 1 ))) (PreH14 : ((j - 1 ) < n_pre)) (PreH15 : (0 <= ((stride * i ) + j ))) (PreH16 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH18 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH20 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH22 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (n_pre <= INT_MAX)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (stride = (n_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 1000)) (PreH29 : ((Zlength (xs)) = n_pre)) (PreH30 : ((Zlength (ys)) = n_pre)) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (0 <= ((stride * i ) + j ))) (PreH36 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH37 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) ,
  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.undef_seg table_pre (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
|--
  “ ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0))))) ” 
  &&  “ ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0)) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + (j - 1 ) )) ” 
  &&  “ (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * (i - 1 ) ) + j )) ” 
  &&  “ (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (0 <= ((stride * i ) + (j - 1 ) )) ” 
  &&  “ (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((stride * i ) + j )) ” 
  &&  “ (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ”
  &&  (((table_pre + (((stride * i ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i table_pre ((stride * i ) + j ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((table_pre + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((table_pre + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg table_pre 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg table_pre ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
.

Definition lcs_n_partial_solve_wit_13 := 
forall (table_pre: Z) (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH2 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (stride = (n_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (xs)) = n_pre)) (PreH7 : ((Zlength (ys)) = n_pre)) (PreH8 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full table_pre ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
|--
  “ (0 <= ((stride * n_pre ) + n_pre )) ” 
  &&  “ (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) ) ” 
  &&  “ (LCSNTableResult xs ys n_pre table_l ) ”
  &&  (((table_pre + (((stride * n_pre ) + n_pre ) * sizeof(INT)))) # Int  |-> (Znth ((stride * n_pre ) + n_pre ) table_l 0))
  **  (IntArray.missing_i table_pre ((stride * n_pre ) + n_pre ) 0 ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
.

Definition lcs_n_which_implies_wit_1 := 
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (table_l_2: (@list Z)) (mixed_table_2: (@list (@option Z))) (i: Z) (j: Z) (table: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (IntArray.mixed_full table ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))))) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre) ”
  &&  (IntArray.mixed_seg table 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((table + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg table (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (table_l_2: (@list Z)) (mixed_table_2: (@list (@option Z))) (i: Z) (j: Z) (table: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (IntArray.mixed_full table ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))))) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre) ”
  &&  (IntArray.mixed_seg table 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((table + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg table (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
).

Definition lcs_n_which_implies_wit_2 := 
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (table_l_2: (@list Z)) (mixed_table_2: (@list (@option Z))) (i: Z) (j: Z) (table: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (IntArray.mixed_full table ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ”
  &&  (IntArray.mixed_seg table 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((table + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((table + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg table (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (table_l_2: (@list Z)) (mixed_table_2: (@list (@option Z))) (i: Z) (j: Z) (table: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) ,
  (IntArray.mixed_full table ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ”
  &&  (IntArray.mixed_seg table 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((table + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((table + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg table (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg table ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
).

Module Type VC_Correct.


Axiom proof_of_lcs_n_safety_wit_1 : lcs_n_safety_wit_1.
Axiom proof_of_lcs_n_safety_wit_2 : lcs_n_safety_wit_2.
Axiom proof_of_lcs_n_safety_wit_3 : lcs_n_safety_wit_3.
Axiom proof_of_lcs_n_safety_wit_4 : lcs_n_safety_wit_4.
Axiom proof_of_lcs_n_safety_wit_5 : lcs_n_safety_wit_5.
Axiom proof_of_lcs_n_safety_wit_6 : lcs_n_safety_wit_6.
Axiom proof_of_lcs_n_safety_wit_7 : lcs_n_safety_wit_7.
Axiom proof_of_lcs_n_safety_wit_8 : lcs_n_safety_wit_8.
Axiom proof_of_lcs_n_safety_wit_9 : lcs_n_safety_wit_9.
Axiom proof_of_lcs_n_safety_wit_10 : lcs_n_safety_wit_10.
Axiom proof_of_lcs_n_safety_wit_11 : lcs_n_safety_wit_11.
Axiom proof_of_lcs_n_safety_wit_12 : lcs_n_safety_wit_12.
Axiom proof_of_lcs_n_safety_wit_13 : lcs_n_safety_wit_13.
Axiom proof_of_lcs_n_safety_wit_14 : lcs_n_safety_wit_14.
Axiom proof_of_lcs_n_safety_wit_15 : lcs_n_safety_wit_15.
Axiom proof_of_lcs_n_safety_wit_16 : lcs_n_safety_wit_16.
Axiom proof_of_lcs_n_safety_wit_17 : lcs_n_safety_wit_17.
Axiom proof_of_lcs_n_safety_wit_18 : lcs_n_safety_wit_18.
Axiom proof_of_lcs_n_safety_wit_19 : lcs_n_safety_wit_19.
Axiom proof_of_lcs_n_safety_wit_20 : lcs_n_safety_wit_20.
Axiom proof_of_lcs_n_safety_wit_21 : lcs_n_safety_wit_21.
Axiom proof_of_lcs_n_safety_wit_22 : lcs_n_safety_wit_22.
Axiom proof_of_lcs_n_safety_wit_23 : lcs_n_safety_wit_23.
Axiom proof_of_lcs_n_safety_wit_24 : lcs_n_safety_wit_24.
Axiom proof_of_lcs_n_safety_wit_25 : lcs_n_safety_wit_25.
Axiom proof_of_lcs_n_safety_wit_26 : lcs_n_safety_wit_26.
Axiom proof_of_lcs_n_safety_wit_27 : lcs_n_safety_wit_27.
Axiom proof_of_lcs_n_safety_wit_28 : lcs_n_safety_wit_28.
Axiom proof_of_lcs_n_safety_wit_29 : lcs_n_safety_wit_29.
Axiom proof_of_lcs_n_safety_wit_30 : lcs_n_safety_wit_30.
Axiom proof_of_lcs_n_safety_wit_31 : lcs_n_safety_wit_31.
Axiom proof_of_lcs_n_safety_wit_32 : lcs_n_safety_wit_32.
Axiom proof_of_lcs_n_safety_wit_33 : lcs_n_safety_wit_33.
Axiom proof_of_lcs_n_safety_wit_34 : lcs_n_safety_wit_34.
Axiom proof_of_lcs_n_safety_wit_35 : lcs_n_safety_wit_35.
Axiom proof_of_lcs_n_safety_wit_36 : lcs_n_safety_wit_36.
Axiom proof_of_lcs_n_safety_wit_37 : lcs_n_safety_wit_37.
Axiom proof_of_lcs_n_safety_wit_38 : lcs_n_safety_wit_38.
Axiom proof_of_lcs_n_safety_wit_39 : lcs_n_safety_wit_39.
Axiom proof_of_lcs_n_safety_wit_40 : lcs_n_safety_wit_40.
Axiom proof_of_lcs_n_safety_wit_41 : lcs_n_safety_wit_41.
Axiom proof_of_lcs_n_safety_wit_42 : lcs_n_safety_wit_42.
Axiom proof_of_lcs_n_safety_wit_43 : lcs_n_safety_wit_43.
Axiom proof_of_lcs_n_safety_wit_44 : lcs_n_safety_wit_44.
Axiom proof_of_lcs_n_safety_wit_45 : lcs_n_safety_wit_45.
Axiom proof_of_lcs_n_entail_wit_1 : lcs_n_entail_wit_1.
Axiom proof_of_lcs_n_entail_wit_2 : lcs_n_entail_wit_2.
Axiom proof_of_lcs_n_entail_wit_3 : lcs_n_entail_wit_3.
Axiom proof_of_lcs_n_entail_wit_4 : lcs_n_entail_wit_4.
Axiom proof_of_lcs_n_entail_wit_5 : lcs_n_entail_wit_5.
Axiom proof_of_lcs_n_entail_wit_6 : lcs_n_entail_wit_6.
Axiom proof_of_lcs_n_entail_wit_7 : lcs_n_entail_wit_7.
Axiom proof_of_lcs_n_entail_wit_8 : lcs_n_entail_wit_8.
Axiom proof_of_lcs_n_entail_wit_9 : lcs_n_entail_wit_9.
Axiom proof_of_lcs_n_entail_wit_10_1 : lcs_n_entail_wit_10_1.
Axiom proof_of_lcs_n_entail_wit_10_2 : lcs_n_entail_wit_10_2.
Axiom proof_of_lcs_n_entail_wit_10_3 : lcs_n_entail_wit_10_3.
Axiom proof_of_lcs_n_entail_wit_11 : lcs_n_entail_wit_11.
Axiom proof_of_lcs_n_entail_wit_12 : lcs_n_entail_wit_12.
Axiom proof_of_lcs_n_entail_wit_13 : lcs_n_entail_wit_13.
Axiom proof_of_lcs_n_entail_wit_14 : lcs_n_entail_wit_14.
Axiom proof_of_lcs_n_return_wit_1 : lcs_n_return_wit_1.
Axiom proof_of_lcs_n_partial_solve_wit_1 : lcs_n_partial_solve_wit_1.
Axiom proof_of_lcs_n_partial_solve_wit_2 : lcs_n_partial_solve_wit_2.
Axiom proof_of_lcs_n_partial_solve_wit_3 : lcs_n_partial_solve_wit_3.
Axiom proof_of_lcs_n_partial_solve_wit_4 : lcs_n_partial_solve_wit_4.
Axiom proof_of_lcs_n_partial_solve_wit_5_pure : lcs_n_partial_solve_wit_5_pure.
Axiom proof_of_lcs_n_partial_solve_wit_5 : lcs_n_partial_solve_wit_5.
Axiom proof_of_lcs_n_partial_solve_wit_6 : lcs_n_partial_solve_wit_6.
Axiom proof_of_lcs_n_partial_solve_wit_7 : lcs_n_partial_solve_wit_7.
Axiom proof_of_lcs_n_partial_solve_wit_8_pure : lcs_n_partial_solve_wit_8_pure.
Axiom proof_of_lcs_n_partial_solve_wit_8 : lcs_n_partial_solve_wit_8.
Axiom proof_of_lcs_n_partial_solve_wit_9 : lcs_n_partial_solve_wit_9.
Axiom proof_of_lcs_n_partial_solve_wit_10 : lcs_n_partial_solve_wit_10.
Axiom proof_of_lcs_n_partial_solve_wit_11 : lcs_n_partial_solve_wit_11.
Axiom proof_of_lcs_n_partial_solve_wit_12 : lcs_n_partial_solve_wit_12.
Axiom proof_of_lcs_n_partial_solve_wit_13 : lcs_n_partial_solve_wit_13.
Axiom proof_of_lcs_n_which_implies_wit_1 : lcs_n_which_implies_wit_1.
Axiom proof_of_lcs_n_which_implies_wit_2 : lcs_n_which_implies_wit_2.

End VC_Correct.
