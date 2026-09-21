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
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_common_sequence.longest_common_sequence_lib.
Local Open Scope sac.

(*----- Function longest_common_sequence -----*)

Definition longest_common_sequence_safety_wit_1 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stride" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "table" ) ) 1002001 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition longest_common_sequence_safety_wit_2 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stride" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "table" ) ) 1002001 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_3 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "stride" ) )) # Int  |-> (n_pre + 1 ))
  **  (IntArray.undef_full ( &( "table" ) ) 1002001 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_common_sequence_safety_wit_4 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition longest_common_sequence_safety_wit_5 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_common_sequence_safety_wit_6 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth ((stride * i )) ((Some (0))) (mixed_table)) )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longest_common_sequence_safety_wit_7 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth ((stride * i )) ((Some (0))) (mixed_table)) )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_8 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH12 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_9 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition longest_common_sequence_safety_wit_10 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth (j) ((Some (0))) (mixed_table)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition longest_common_sequence_safety_wit_11 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth (j) ((Some (0))) (mixed_table)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_12 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_13 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table table_l n_pre i )) (PreH12 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_14 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition longest_common_sequence_safety_wit_15 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition longest_common_sequence_safety_wit_16 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_17 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_18 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((stride * i ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + j )) ”
.

Definition longest_common_sequence_safety_wit_19 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition longest_common_sequence_safety_wit_20 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) + 1 )) ”
.

Definition longest_common_sequence_safety_wit_21 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((stride * (i - 1 ) ) + (j - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * (i - 1 ) ) + (j - 1 ) )) ”
.

Definition longest_common_sequence_safety_wit_22 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition longest_common_sequence_safety_wit_23 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * (i - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * (i - 1 ) )) ”
.

Definition longest_common_sequence_safety_wit_24 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition longest_common_sequence_safety_wit_25 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_26 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_27 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_28 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((stride * (i - 1 ) ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * (i - 1 ) ) + j )) ”
.

Definition longest_common_sequence_safety_wit_29 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * (i - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * (i - 1 ) )) ”
.

Definition longest_common_sequence_safety_wit_30 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition longest_common_sequence_safety_wit_31 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_32 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((stride * i ) + (j - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + (j - 1 ) )) ”
.

Definition longest_common_sequence_safety_wit_33 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition longest_common_sequence_safety_wit_34 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition longest_common_sequence_safety_wit_35 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_36 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((stride * i ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + j )) ”
.

Definition longest_common_sequence_safety_wit_37 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition longest_common_sequence_safety_wit_38 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((stride * i ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * i ) + j )) ”
.

Definition longest_common_sequence_safety_wit_39 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * i )) ”
.

Definition longest_common_sequence_safety_wit_40 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (i: Z) (j: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1 ))) (PreH11 : ((j + 1 ) <= (n_pre + 1 ))) (PreH12 : (0 <= ((stride * i ) + (j + 1 ) ))) (PreH13 : (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) )) (PreH15 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition longest_common_sequence_safety_wit_41 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (i: Z) (j: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1 ))) (PreH11 : ((j + 1 ) <= (n_pre + 1 ))) (PreH12 : (0 <= ((stride * i ) + (j + 1 ) ))) (PreH13 : (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1 ) )) (PreH15 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_42 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH14 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition longest_common_sequence_safety_wit_43 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH14 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition longest_common_sequence_safety_wit_44 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) (PreH10 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH11 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (((stride * n_pre ) + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((stride * n_pre ) + n_pre )) ”
.

Definition longest_common_sequence_safety_wit_45 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) (PreH10 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH11 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((stride * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (stride * n_pre )) ”
.

Definition longest_common_sequence_entail_wit_1 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (IntArray.undef_full ( &( "table" ) ) 1002001 )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (IntArray.undef_full ( &( "table" ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
).

Definition longest_common_sequence_entail_wit_2 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH12 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (0 <= (stride * i ))) (PreH16 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH18 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  “ (((n_pre + 1 ) * i ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1 ))) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : (0 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (0 <= (stride * i ))) (PreH16 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH18 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((n_pre + 1 ) * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition longest_common_sequence_entail_wit_3 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) (PreH16 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth ((stride * i )) ((Some (0))) (mixed_table_2)) )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) (PreH16 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= (((Zlength (xs)) + 1 ) * (i + 1 ) )) ” 
  &&  “ ((((Zlength (xs)) + 1 ) * (i + 1 ) ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNColumnProgress (replace_Znth ((((Zlength (xs)) + 1 ) * i )) ((Some (0))) (mixed_table_2)) table_l (Zlength (xs)) (i + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth ((((Zlength (xs)) + 1 ) * i )) ((Some (0))) (mixed_table_2)))) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_4 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i )) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (LCSNBoundaryProgress mixed_table_2 table_l (Zlength (xs)) 1 ) ” 
  &&  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_5 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) (replace_Znth (j) ((Some (0))) (mixed_table_2)) )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (LCSNBoundaryProgress (replace_Znth (j) ((Some (0))) (mixed_table_2)) table_l (Zlength (xs)) (j + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (j) ((Some (0))) (mixed_table_2)))) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_6 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j )) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= (((Zlength (xs)) + 1 ) * 1 )) ” 
  &&  “ ((((Zlength (xs)) + 1 ) * 1 ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) 1 ) ” 
  &&  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_7 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= ((((Zlength (xs)) + 1 ) * i ) + 1 )) ” 
  &&  “ (((((Zlength (xs)) + 1 ) * i ) + 1 ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table_2 table_l (Zlength (xs)) i 1 ) ” 
  &&  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_8 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH14 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  “ ((((n_pre + 1 ) * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((((n_pre + 1 ) * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((((n_pre + 1 ) * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition longest_common_sequence_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition longest_common_sequence_entail_wit_8_split_goal_3 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1 ))) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1 ))) (PreH19 : (0 <= ((stride * i ) + j ))) (PreH20 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((((n_pre + 1 ) * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))
.

Definition longest_common_sequence_entail_wit_9_1 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH6 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH40 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.undef_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) + 1 ))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= INT_MAX)) (PreH2 : (((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) + 1 ) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) >= INT_MIN)) (PreH4 : (((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) + 1 ) >= INT_MIN)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH13 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH14 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))) (PreH15 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) <= n_pre)) (PreH16 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH17 : (0 <= (i - 1 ))) (PreH18 : ((i - 1 ) < n_pre)) (PreH19 : (0 <= (j - 1 ))) (PreH20 : ((j - 1 ) < n_pre)) (PreH21 : (0 <= ((stride * i ) + j ))) (PreH22 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH24 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH26 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH28 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : (n_pre <= INT_MAX)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= n_pre)) (PreH32 : (stride = (n_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 1000)) (PreH35 : ((Zlength (xs)) = n_pre)) (PreH36 : ((Zlength (ys)) = n_pre)) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (0 <= ((stride * i ) + j ))) (PreH42 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH43 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH44 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH45 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)) + 1 ))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
).

Definition longest_common_sequence_entail_wit_9_2 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH40 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.undef_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH11 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH14 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH15 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH16 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH17 : (0 <= (i - 1 ))) (PreH18 : ((i - 1 ) < n_pre)) (PreH19 : (0 <= (j - 1 ))) (PreH20 : ((j - 1 ) < n_pre)) (PreH21 : (0 <= ((stride * i ) + j ))) (PreH22 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH24 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH26 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH28 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : (n_pre <= INT_MAX)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= n_pre)) (PreH32 : (stride = (n_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 1000)) (PreH35 : ((Zlength (xs)) = n_pre)) (PreH36 : ((Zlength (ys)) = n_pre)) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (0 <= ((stride * i ) + j ))) (PreH42 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH43 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH44 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH45 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
).

Definition longest_common_sequence_entail_wit_9_3 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH7 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH40 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.undef_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "above" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  ((( &( "left" ) )) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH11 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table_2) (None)) = None)) (PreH14 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))))) (PreH15 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))))) (PreH16 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH17 : (0 <= (i - 1 ))) (PreH18 : ((i - 1 ) < n_pre)) (PreH19 : (0 <= (j - 1 ))) (PreH20 : ((j - 1 ) < n_pre)) (PreH21 : (0 <= ((stride * i ) + j ))) (PreH22 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH24 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH26 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH28 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : (n_pre <= INT_MAX)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= n_pre)) (PreH32 : (stride = (n_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 1000)) (PreH35 : ((Zlength (xs)) = n_pre)) (PreH36 : ((Zlength (ys)) = n_pre)) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (0 <= ((stride * i ) + j ))) (PreH42 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH43 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH44 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH45 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l_2) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l_2) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table_2)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table_2)) )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
).

Definition longest_common_sequence_entail_wit_10 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (stride: Z) (i: Z) (j: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1 ))) (PreH11 : ((j + 1 ) <= (n_pre + 1 ))) (PreH12 : (0 <= ((stride * i ) + (j + 1 ) ))) (PreH13 : (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i (j + 1 ) )) (PreH15 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (stride: Z) (i: Z) (j: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1 ))) (PreH11 : ((j + 1 ) <= (n_pre + 1 ))) (PreH12 : (0 <= ((stride * i ) + (j + 1 ) ))) (PreH13 : (((stride * i ) + (j + 1 ) ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i (j + 1 ) )) (PreH15 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH16 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (LCSNRowProgress xs ys mixed_table_2 table_l (Zlength (xs)) i (j + 1 ) ) ” 
  &&  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_11 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH14 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (j: Z) (i: Z) (stride: Z) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1 ))) (PreH11 : (0 <= ((stride * i ) + j ))) (PreH12 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j )) (PreH14 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  TT && emp 
|--
  EX (table_l: (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((Zlength (xs)) + 1 )) ” 
  &&  “ (0 <= (((Zlength (xs)) + 1 ) * (i + 1 ) )) ” 
  &&  “ ((((Zlength (xs)) + 1 ) * (i + 1 ) ) <= (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) (i + 1 ) ) ” 
  &&  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1 ) * ((Zlength (xs)) + 1 ) )) ”
  &&  emp
).

Definition longest_common_sequence_entail_wit_12 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNTableResult xs ys n_pre table_l ) ” 
  &&  “ (0 <= ((stride * n_pre ) + n_pre )) ” 
  &&  “ (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table_2: (@list (@option Z))) (table_l_2: (@list Z)) (i: Z) (stride: Z) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (0 <= (stride * i ))) (PreH10 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i )) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table_2 )
|--
  EX (mixed_table: (@list (@option Z)))  (table_l: (@list Z)) ,
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNTableResult xs ys n_pre table_l ) ” 
  &&  “ (0 <= ((stride * n_pre ) + n_pre )) ” 
  &&  “ (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
).

Definition longest_common_sequence_entail_wit_13 := 
(
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) (PreH10 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH11 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (LCSNLength xs ys (Znth ((stride * n_pre ) + n_pre ) table_l 0) ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_full ( &( "table" ) ) 1002001 )
  **  ((( &( "stride" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) (PreH10 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH11 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (LCSNLength xs ys (Znth (((n_pre + 1 ) * n_pre ) + n_pre ) table_l 0) ) ”
  &&  (IntArray.undef_full ( &( "table" ) ) 1002001 )
).

Definition longest_common_sequence_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) (PreH10 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH11 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (LCSNLength xs ys (Znth (((n_pre + 1 ) * n_pre ) + n_pre ) table_l 0) ) ”
.

Definition longest_common_sequence_entail_wit_13_split_goal_spatial := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) (PreH10 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH11 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  (IntArray.undef_full ( &( "table" ) ) 1002001 )
.

Definition longest_common_sequence_return_wit_1 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (result: Z) (PreH1 : (LCSNLength xs ys result )) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
|--
  “ (LCSNLength xs ys result ) ”
  &&  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
.

Definition longest_common_sequence_partial_solve_wit_1 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (stride: Z) (PreH1 : (0 <= (stride * i ))) (PreH2 : ((stride * i ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1 ))) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (stride * i ))) (PreH14 : ((stride * i ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i )) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + ((stride * i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i ( &( "table" ) ) (stride * i ) 0 ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_2 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (j: Z) (stride: Z) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1 ))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j )) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (j <= n_pre) ” 
  &&  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (LCSNBoundaryProgress mixed_table table_l n_pre j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.mixed_missing_i ( &( "table" ) ) j 0 ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_3 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((x_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) xs 0))
  **  (IntArray.missing_i x_pre (i - 1 ) 0 n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_4 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (0 <= (j - 1 ))) (PreH4 : ((j - 1 ) < n_pre)) (PreH5 : (0 <= ((stride * i ) + j ))) (PreH6 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH8 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH10 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH11 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH12 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (0 <= ((stride * i ) + j ))) (PreH26 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((y_pre + ((j - 1 ) * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) ys 0))
  **  (IntArray.missing_i y_pre (j - 1 ) 0 n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_5_pure := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition longest_common_sequence_partial_solve_wit_5_aux := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_5 := longest_common_sequence_partial_solve_wit_5_pure -> longest_common_sequence_partial_solve_wit_5_aux.

Definition longest_common_sequence_partial_solve_wit_6 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))))) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_7 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))))) (PreH10 : (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))) (PreH11 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre)) (PreH12 : ((Znth (i - 1 ) xs 0) = (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))))) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i ( &( "table" ) ) ((stride * i ) + j ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_8_pure := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "stride" ) )) # Int  |-> stride)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  ((( &( "above" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition longest_common_sequence_partial_solve_wit_8_aux := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH2 : (0 <= (i - 1 ))) (PreH3 : ((i - 1 ) < n_pre)) (PreH4 : (0 <= (j - 1 ))) (PreH5 : ((j - 1 ) < n_pre)) (PreH6 : (0 <= ((stride * i ) + j ))) (PreH7 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH9 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH10 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH11 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH12 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH13 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1 ))) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1 ))) (PreH26 : (0 <= ((stride * i ) + j ))) (PreH27 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_8 := longest_common_sequence_partial_solve_wit_8_pure -> longest_common_sequence_partial_solve_wit_8_aux.

Definition longest_common_sequence_partial_solve_wit_9 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_10 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH10 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH11 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (0 <= (j - 1 ))) (PreH15 : ((j - 1 ) < n_pre)) (PreH16 : (0 <= ((stride * i ) + j ))) (PreH17 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH18 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH19 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH20 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH21 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH22 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH23 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1 ))) (PreH36 : (0 <= ((stride * i ) + j ))) (PreH37 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_11 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) >= (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i ( &( "table" ) ) ((stride * i ) + j ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_12 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (j: Z) (i: Z) (stride: Z) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (PreH1 : ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))))) (PreH11 : ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))))) (PreH12 : ((Znth (i - 1 ) xs 0) <> (Znth (j - 1 ) ys 0))) (PreH13 : (0 <= (i - 1 ))) (PreH14 : ((i - 1 ) < n_pre)) (PreH15 : (0 <= (j - 1 ))) (PreH16 : ((j - 1 ) < n_pre)) (PreH17 : (0 <= ((stride * i ) + j ))) (PreH18 : (((stride * i ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH19 : (0 <= ((stride * (i - 1 ) ) + (j - 1 ) ))) (PreH20 : (((stride * (i - 1 ) ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH21 : (0 <= ((stride * (i - 1 ) ) + j ))) (PreH22 : (((stride * (i - 1 ) ) + j ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH23 : (0 <= ((stride * i ) + (j - 1 ) ))) (PreH24 : (((stride * i ) + (j - 1 ) ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1 ))) (PreH37 : (0 <= ((stride * i ) + j ))) (PreH38 : (((stride * i ) + j ) <= ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ ((Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)) < (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ” 
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
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (((stride * i ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_missing_i ( &( "table" ) ) ((stride * i ) + j ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (((( &( "table" ) ) + (((stride * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (((( &( "table" ) ) + (((stride * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth (((((Zlength (xs)) + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_partial_solve_wit_13 := 
forall (n_pre: Z) (y_pre: Z) (x_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (stride: Z) (PreH1 : (stride = (n_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) )) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH9 : (LCSNTableResult xs ys n_pre table_l )) (PreH10 : (0 <= ((stride * n_pre ) + n_pre ))) (PreH11 : (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
|--
  “ (stride = (n_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1000) ” 
  &&  “ ((Zlength (xs)) = n_pre) ” 
  &&  “ ((Zlength (ys)) = n_pre) ” 
  &&  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1 ) ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (LCSNTableResult xs ys n_pre table_l ) ” 
  &&  “ (0 <= ((stride * n_pre ) + n_pre )) ” 
  &&  “ (((stride * n_pre ) + n_pre ) < ((n_pre + 1 ) * (n_pre + 1 ) )) ”
  &&  (((( &( "table" ) ) + (((stride * n_pre ) + n_pre ) * sizeof(INT)))) # Int  |-> (Znth ((stride * n_pre ) + n_pre ) table_l 0))
  **  (IntArray.missing_i ( &( "table" ) ) ((stride * n_pre ) + n_pre ) 0 ((n_pre + 1 ) * (n_pre + 1 ) ) table_l )
  **  (IntArray.full x_pre n_pre xs )
  **  (IntArray.full y_pre n_pre ys )
  **  (IntArray.undef_seg ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) 1002001 )
.

Definition longest_common_sequence_which_implies_wit_1 := 
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))))) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre) ”
  &&  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre) ” 
  &&  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ”
  &&  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
).

Definition longest_common_sequence_which_implies_wit_1_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)) <= n_pre) ”
.

Definition longest_common_sequence_which_implies_wit_1_split_goal_2 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (0 <= (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))) ”
.

Definition longest_common_sequence_which_implies_wit_1_split_goal_3 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0))))) ”
.

Definition longest_common_sequence_which_implies_wit_1_split_goal_4 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ”
.

Definition longest_common_sequence_which_implies_wit_1_split_goal_spatial := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 ) (((n_pre + 1 ) * i ) + j ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + (j - 1 ) ) + 1 )) ((((n_pre + 1 ) * i ) + j )) (mixed_table)) )
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
.

Definition longest_common_sequence_which_implies_wit_2 := 
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j ) ” 
  &&  “ ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ”
  &&  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
) \/
(
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ” 
  &&  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ”
  &&  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
).

Definition longest_common_sequence_which_implies_wit_2_split_goal_1 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0))))) ”
.

Definition longest_common_sequence_which_implies_wit_2_split_goal_2 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0))))) ”
.

Definition longest_common_sequence_which_implies_wit_2_split_goal_3 := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  “ ((Znth ((((n_pre + 1 ) * i ) + j )) (mixed_table) (None)) = None) ”
.

Definition longest_common_sequence_which_implies_wit_2_split_goal_spatial := 
forall (n_pre: Z) (ys: (@list Z)) (xs: (@list Z)) (mixed_table: (@list (@option Z))) (table_l: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j )) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1 ) * (n_pre + 1 ) ))) ,
  (IntArray.mixed_full ( &( "table" ) ) ((n_pre + 1 ) * (n_pre + 1 ) ) mixed_table )
|--
  (IntArray.mixed_seg ( &( "table" ) ) 0 (((n_pre + 1 ) * (i - 1 ) ) + j ) (sublist (0) ((((n_pre + 1 ) * (i - 1 ) ) + j )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * (i - 1 ) ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * (i - 1 ) ) + j )) (table_l) (0)))
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 ) (((n_pre + 1 ) * i ) + (j - 1 ) ) (sublist (((((n_pre + 1 ) * (i - 1 ) ) + j ) + 1 )) ((((n_pre + 1 ) * i ) + (j - 1 ) )) (mixed_table)) )
  **  (((( &( "table" ) ) + ((((n_pre + 1 ) * i ) + (j - 1 ) ) * sizeof(INT)))) # Int  |-> (Znth ((((n_pre + 1 ) * i ) + (j - 1 ) )) (table_l) (0)))
  **  (IntArray.undef_seg ( &( "table" ) ) (((n_pre + 1 ) * i ) + j ) ((((n_pre + 1 ) * i ) + j ) + 1 ) )
  **  (IntArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1 ) * i ) + j ) + 1 ) ((n_pre + 1 ) * (n_pre + 1 ) ) (sublist (((((n_pre + 1 ) * i ) + j ) + 1 )) (((n_pre + 1 ) * (n_pre + 1 ) )) (mixed_table)) )
.

Module Type VC_Correct.


Axiom proof_of_longest_common_sequence_safety_wit_1 : longest_common_sequence_safety_wit_1.
Axiom proof_of_longest_common_sequence_safety_wit_2 : longest_common_sequence_safety_wit_2.
Axiom proof_of_longest_common_sequence_safety_wit_3 : longest_common_sequence_safety_wit_3.
Axiom proof_of_longest_common_sequence_safety_wit_4 : longest_common_sequence_safety_wit_4.
Axiom proof_of_longest_common_sequence_safety_wit_5 : longest_common_sequence_safety_wit_5.
Axiom proof_of_longest_common_sequence_safety_wit_6 : longest_common_sequence_safety_wit_6.
Axiom proof_of_longest_common_sequence_safety_wit_7 : longest_common_sequence_safety_wit_7.
Axiom proof_of_longest_common_sequence_safety_wit_8 : longest_common_sequence_safety_wit_8.
Axiom proof_of_longest_common_sequence_safety_wit_9 : longest_common_sequence_safety_wit_9.
Axiom proof_of_longest_common_sequence_safety_wit_10 : longest_common_sequence_safety_wit_10.
Axiom proof_of_longest_common_sequence_safety_wit_11 : longest_common_sequence_safety_wit_11.
Axiom proof_of_longest_common_sequence_safety_wit_12 : longest_common_sequence_safety_wit_12.
Axiom proof_of_longest_common_sequence_safety_wit_13 : longest_common_sequence_safety_wit_13.
Axiom proof_of_longest_common_sequence_safety_wit_14 : longest_common_sequence_safety_wit_14.
Axiom proof_of_longest_common_sequence_safety_wit_15 : longest_common_sequence_safety_wit_15.
Axiom proof_of_longest_common_sequence_safety_wit_16 : longest_common_sequence_safety_wit_16.
Axiom proof_of_longest_common_sequence_safety_wit_17 : longest_common_sequence_safety_wit_17.
Axiom proof_of_longest_common_sequence_safety_wit_18 : longest_common_sequence_safety_wit_18.
Axiom proof_of_longest_common_sequence_safety_wit_19 : longest_common_sequence_safety_wit_19.
Axiom proof_of_longest_common_sequence_safety_wit_20 : longest_common_sequence_safety_wit_20.
Axiom proof_of_longest_common_sequence_safety_wit_21 : longest_common_sequence_safety_wit_21.
Axiom proof_of_longest_common_sequence_safety_wit_22 : longest_common_sequence_safety_wit_22.
Axiom proof_of_longest_common_sequence_safety_wit_23 : longest_common_sequence_safety_wit_23.
Axiom proof_of_longest_common_sequence_safety_wit_24 : longest_common_sequence_safety_wit_24.
Axiom proof_of_longest_common_sequence_safety_wit_25 : longest_common_sequence_safety_wit_25.
Axiom proof_of_longest_common_sequence_safety_wit_26 : longest_common_sequence_safety_wit_26.
Axiom proof_of_longest_common_sequence_safety_wit_27 : longest_common_sequence_safety_wit_27.
Axiom proof_of_longest_common_sequence_safety_wit_28 : longest_common_sequence_safety_wit_28.
Axiom proof_of_longest_common_sequence_safety_wit_29 : longest_common_sequence_safety_wit_29.
Axiom proof_of_longest_common_sequence_safety_wit_30 : longest_common_sequence_safety_wit_30.
Axiom proof_of_longest_common_sequence_safety_wit_31 : longest_common_sequence_safety_wit_31.
Axiom proof_of_longest_common_sequence_safety_wit_32 : longest_common_sequence_safety_wit_32.
Axiom proof_of_longest_common_sequence_safety_wit_33 : longest_common_sequence_safety_wit_33.
Axiom proof_of_longest_common_sequence_safety_wit_34 : longest_common_sequence_safety_wit_34.
Axiom proof_of_longest_common_sequence_safety_wit_35 : longest_common_sequence_safety_wit_35.
Axiom proof_of_longest_common_sequence_safety_wit_36 : longest_common_sequence_safety_wit_36.
Axiom proof_of_longest_common_sequence_safety_wit_37 : longest_common_sequence_safety_wit_37.
Axiom proof_of_longest_common_sequence_safety_wit_38 : longest_common_sequence_safety_wit_38.
Axiom proof_of_longest_common_sequence_safety_wit_39 : longest_common_sequence_safety_wit_39.
Axiom proof_of_longest_common_sequence_safety_wit_40 : longest_common_sequence_safety_wit_40.
Axiom proof_of_longest_common_sequence_safety_wit_41 : longest_common_sequence_safety_wit_41.
Axiom proof_of_longest_common_sequence_safety_wit_42 : longest_common_sequence_safety_wit_42.
Axiom proof_of_longest_common_sequence_safety_wit_43 : longest_common_sequence_safety_wit_43.
Axiom proof_of_longest_common_sequence_safety_wit_44 : longest_common_sequence_safety_wit_44.
Axiom proof_of_longest_common_sequence_safety_wit_45 : longest_common_sequence_safety_wit_45.
Axiom proof_of_longest_common_sequence_entail_wit_1 : longest_common_sequence_entail_wit_1.
Axiom proof_of_longest_common_sequence_entail_wit_2 : longest_common_sequence_entail_wit_2.
Axiom proof_of_longest_common_sequence_entail_wit_3 : longest_common_sequence_entail_wit_3.
Axiom proof_of_longest_common_sequence_entail_wit_4 : longest_common_sequence_entail_wit_4.
Axiom proof_of_longest_common_sequence_entail_wit_5 : longest_common_sequence_entail_wit_5.
Axiom proof_of_longest_common_sequence_entail_wit_6 : longest_common_sequence_entail_wit_6.
Axiom proof_of_longest_common_sequence_entail_wit_7 : longest_common_sequence_entail_wit_7.
Axiom proof_of_longest_common_sequence_entail_wit_8 : longest_common_sequence_entail_wit_8.
Axiom proof_of_longest_common_sequence_entail_wit_9_1 : longest_common_sequence_entail_wit_9_1.
Axiom proof_of_longest_common_sequence_entail_wit_9_2 : longest_common_sequence_entail_wit_9_2.
Axiom proof_of_longest_common_sequence_entail_wit_9_3 : longest_common_sequence_entail_wit_9_3.
Axiom proof_of_longest_common_sequence_entail_wit_10 : longest_common_sequence_entail_wit_10.
Axiom proof_of_longest_common_sequence_entail_wit_11 : longest_common_sequence_entail_wit_11.
Axiom proof_of_longest_common_sequence_entail_wit_12 : longest_common_sequence_entail_wit_12.
Axiom proof_of_longest_common_sequence_entail_wit_13 : longest_common_sequence_entail_wit_13.
Axiom proof_of_longest_common_sequence_return_wit_1 : longest_common_sequence_return_wit_1.
Axiom proof_of_longest_common_sequence_partial_solve_wit_1 : longest_common_sequence_partial_solve_wit_1.
Axiom proof_of_longest_common_sequence_partial_solve_wit_2 : longest_common_sequence_partial_solve_wit_2.
Axiom proof_of_longest_common_sequence_partial_solve_wit_3 : longest_common_sequence_partial_solve_wit_3.
Axiom proof_of_longest_common_sequence_partial_solve_wit_4 : longest_common_sequence_partial_solve_wit_4.
Axiom proof_of_longest_common_sequence_partial_solve_wit_5_pure : longest_common_sequence_partial_solve_wit_5_pure.
Axiom proof_of_longest_common_sequence_partial_solve_wit_5 : longest_common_sequence_partial_solve_wit_5.
Axiom proof_of_longest_common_sequence_partial_solve_wit_6 : longest_common_sequence_partial_solve_wit_6.
Axiom proof_of_longest_common_sequence_partial_solve_wit_7 : longest_common_sequence_partial_solve_wit_7.
Axiom proof_of_longest_common_sequence_partial_solve_wit_8_pure : longest_common_sequence_partial_solve_wit_8_pure.
Axiom proof_of_longest_common_sequence_partial_solve_wit_8 : longest_common_sequence_partial_solve_wit_8.
Axiom proof_of_longest_common_sequence_partial_solve_wit_9 : longest_common_sequence_partial_solve_wit_9.
Axiom proof_of_longest_common_sequence_partial_solve_wit_10 : longest_common_sequence_partial_solve_wit_10.
Axiom proof_of_longest_common_sequence_partial_solve_wit_11 : longest_common_sequence_partial_solve_wit_11.
Axiom proof_of_longest_common_sequence_partial_solve_wit_12 : longest_common_sequence_partial_solve_wit_12.
Axiom proof_of_longest_common_sequence_partial_solve_wit_13 : longest_common_sequence_partial_solve_wit_13.
Axiom proof_of_longest_common_sequence_which_implies_wit_1 : longest_common_sequence_which_implies_wit_1.
Axiom proof_of_longest_common_sequence_which_implies_wit_2 : longest_common_sequence_which_implies_wit_2.

End VC_Correct.
