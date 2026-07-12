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
Require Import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function energyNecklace -----*)

Definition energyNecklace_safety_wit_1 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : (EnergyLabelsBounded beads_l n_pre )) (PreH5 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full vals_pre (2 * n_pre ) )
  **  (IntArray.undef_full dp_pre ((2 * n_pre ) * (2 * n_pre ) ) )
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition energyNecklace_safety_wit_2 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : (EnergyLabelsBounded beads_l n_pre )) (PreH5 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full vals_pre (2 * n_pre ) )
  **  (IntArray.undef_full dp_pre ((2 * n_pre ) * (2 * n_pre ) ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition energyNecklace_safety_wit_3 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre )) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full vals_pre total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_4 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg vals_pre 0 (i + 1 ) (app (vals_l) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg vals_pre (i + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition energyNecklace_safety_wit_5 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (vals_l)) = n_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH10 : (EnergyLabelsBounded beads_l n_pre )) (PreH11 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 n_pre vals_l )
  **  (IntArray.undef_seg vals_pre n_pre total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_6 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg vals_pre (n_pre + i ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ ((n_pre + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + i )) ”
.

Definition energyNecklace_safety_wit_7 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg vals_pre 0 ((n_pre + i ) + 1 ) (app (vals_l) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg vals_pre ((n_pre + i ) + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition energyNecklace_safety_wit_8 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH9 : (EnergyLabelsBounded beads_l n_pre )) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_9 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= (total * width ))) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l 0) = 0))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.seg dp_pre 0 i dp_l )
  **  (IntArray.undef_seg dp_pre i (total * width ) )
|--
  “ ((total * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total * width )) ”
.

Definition energyNecklace_safety_wit_10 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.seg dp_pre 0 i dp_l )
  **  (IntArray.undef_seg dp_pre i (total * width ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_11 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) (total * width ) )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition energyNecklace_safety_wit_12 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (total * width ))) (PreH9 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH10 : (EnergyZeroTable dp_l total width )) (PreH11 : (EnergyLenDone vals_l dp_l total width 2 )) (PreH12 : (EnergyLabelsBounded beads_l n_pre )) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition energyNecklace_safety_wit_13 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH13 : (EnergyLenDone vals_l dp_l total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_14 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left <= (total - len ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLeftProgress vals_l dp_l total width len left )) (PreH15 : (EnergyLabelsBounded beads_l n_pre )) (PreH16 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((total - len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total - len )) ”
.

Definition energyNecklace_safety_wit_15 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (((left + len ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + len ) - 1 )) ”
.

Definition energyNecklace_safety_wit_16 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((left + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + len )) ”
.

Definition energyNecklace_safety_wit_17 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_18 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (EnergyLeftProgress vals_l dp_l total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_19 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (((left * width ) + split ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left * width ) + split )) ”
.

Definition energyNecklace_safety_wit_20 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((left * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * width )) ”
.

Definition energyNecklace_safety_wit_21 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
|--
  “ ((((split + 1 ) * width ) + right ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((split + 1 ) * width ) + right )) ”
.

Definition energyNecklace_safety_wit_22 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
|--
  “ (((split + 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((split + 1 ) * width )) ”
.

Definition energyNecklace_safety_wit_23 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition energyNecklace_safety_wit_24 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_25 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ”
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ”
).

Definition energyNecklace_safety_wit_25_split_goal_1 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_25_split_goal_2 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((INT_MIN) <= (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ”
.

Definition energyNecklace_safety_wit_26 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((right + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right + 1 )) ”
.

Definition energyNecklace_safety_wit_27 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) )) ”
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) )) ”
).

Definition energyNecklace_safety_wit_27_split_goal_1 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_27_split_goal_2 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((INT_MIN) <= ((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) )) ”
.

Definition energyNecklace_safety_wit_28 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition energyNecklace_safety_wit_29 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_30 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_31 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ”
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ”
).

Definition energyNecklace_safety_wit_31_split_goal_1 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_31_split_goal_2 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((INT_MIN) <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ”
.

Definition energyNecklace_safety_wit_32 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) )) ”
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) )) ”
).

Definition energyNecklace_safety_wit_32_split_goal_1 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_32_split_goal_2 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full vals_pre total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((INT_MIN) <= ((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) )) ”
.

Definition energyNecklace_safety_wit_33 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1 ) < total)) (PreH15 : (left_value = (Znth ((left * width ) + split ) dp_l 0))) (PreH16 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l 0))) (PreH17 : (gain = (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))) (PreH18 : (candidate = ((left_value + right_value ) + gain ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : (0 <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l)) = (total * width ))) (PreH25 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH26 : (EnergySplitProgress vals_l dp_l total width len left (split + 1 ) best )) (PreH27 : (EnergyLabelsBounded beads_l n_pre )) (PreH28 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition energyNecklace_safety_wit_34 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH20 : (EnergySplitProgress vals_l dp_l total width len left right best )) (PreH21 : (EnergyIntervalBest vals_l left right best )) (PreH22 : (EnergyLabelsBounded beads_l n_pre )) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (((left * width ) + right ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left * width ) + right )) ”
.

Definition energyNecklace_safety_wit_35 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH20 : (EnergySplitProgress vals_l dp_l total width len left right best )) (PreH21 : (EnergyIntervalBest vals_l left right best )) (PreH22 : (EnergyLabelsBounded beads_l n_pre )) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((left * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * width )) ”
.

Definition energyNecklace_safety_wit_36 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_old: (@list Z)) (dp_new: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (0 <= best)) (PreH13 : (best <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_old)) = (total * width ))) (PreH16 : ((Zlength (dp_new)) = (total * width ))) (PreH17 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH18 : (EnergyUpdatedCell vals_l dp_old dp_new width left right best )) (PreH19 : (EnergyLeftProgress vals_l dp_new total width len (left + 1 ) )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_new )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition energyNecklace_safety_wit_37 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l)) = (total * width ))) (PreH11 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH12 : (EnergyLenDone vals_l dp_l total width (len + 1 ) )) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + 1 )) ”
.

Definition energyNecklace_safety_wit_38 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH13 : (EnergyLenDone vals_l dp_l total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_39 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = (total * width ))) (PreH9 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH10 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH11 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width 0 answer )) (PreH12 : (EnergyLabelsBounded beads_l n_pre )) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_40 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (((((start * width ) + start ) + n_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((start * width ) + start ) + n_pre ) - 1 )) ”
.

Definition energyNecklace_safety_wit_41 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((((start * width ) + start ) + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((start * width ) + start ) + n_pre )) ”
.

Definition energyNecklace_safety_wit_42 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (((start * width ) + start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((start * width ) + start )) ”
.

Definition energyNecklace_safety_wit_43 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((start * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start * width )) ”
.

Definition energyNecklace_safety_wit_44 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_45 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0))) (PreH10 : (0 <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l)) = (total * width ))) (PreH16 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH17 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH18 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1 ) answer )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "vals" ) )) # Ptr  |-> vals_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ ((start + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + 1 )) ”
.

Definition energyNecklace_entail_wit_1 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : (EnergyLabelsBounded beads_l n_pre )) (PreH5 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full vals_pre (2 * n_pre ) )
  **  (IntArray.undef_full dp_pre ((2 * n_pre ) * (2 * n_pre ) ) )
|--
  “ ((2 * n_pre ) = (2 * n_pre )) ” 
  &&  “ ((2 * n_pre ) = (2 * n_pre )) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= (2 * n_pre )) ” 
  &&  “ ((2 * n_pre ) <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full vals_pre (2 * n_pre ) )
  **  (IntArray.undef_full dp_pre ((2 * n_pre ) * (2 * n_pre ) ) )
.

Definition energyNecklace_entail_wit_2 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre )) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full vals_pre total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 0 vals_l )
  **  (IntArray.undef_seg vals_pre 0 total )
  **  (IntArray.undef_full dp_pre (total * width ) )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre )) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (IntArray.undef_full dp_pre (total * width ) )
).

Definition energyNecklace_entail_wit_2_split_goal_1 := 
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre )) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition energyNecklace_entail_wit_2_split_goal_spatial := 
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyLabelsBounded beads_l n_pre )) (PreH9 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  (IntArray.undef_full dp_pre (total * width ) )
.

Definition energyNecklace_entail_wit_3 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg vals_pre 0 (i + 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg vals_pre (i + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (i + 1 ) vals_l )
  **  (IntArray.undef_seg vals_pre (i + 1 ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (((Znth 0 (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) 0) = (Znth 0 beads_l 0)) /\ ((Znth ((i + 1 ) - 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) 0) = (Znth ((i + 1 ) - 1 ) beads_l 0))) ” 
  &&  “ ((Zlength ((app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))))) = (i + 1 )) ”
  &&  (IntArray.undef_full dp_pre (total * width ) )
).

Definition energyNecklace_entail_wit_3_split_goal_1 := 
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (((Znth 0 (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) 0) = (Znth 0 beads_l 0)) /\ ((Znth ((i + 1 ) - 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) 0) = (Znth ((i + 1 ) - 1 ) beads_l 0))) ”
.

Definition energyNecklace_entail_wit_3_split_goal_2 := 
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ ((Zlength ((app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))))) = (i + 1 )) ”
.

Definition energyNecklace_entail_wit_3_split_goal_spatial := 
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  (IntArray.undef_full dp_pre (total * width ) )
.

Definition energyNecklace_entail_wit_4 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 i vals_l_2 )
  **  (IntArray.undef_seg vals_pre i total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 n_pre vals_l )
  **  (IntArray.undef_seg vals_pre n_pre total )
  **  (IntArray.undef_full dp_pre (total * width ) )
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg vals_pre 0 i vals_l_2 )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.seg vals_pre 0 n_pre vals_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
).

Definition energyNecklace_entail_wit_5 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (vals_l_2)) = n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 vals_l_2 0) = (Znth k_3 beads_l 0)))) (PreH10 : (EnergyLabelsBounded beads_l n_pre )) (PreH11 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 n_pre vals_l_2 )
  **  (IntArray.undef_seg vals_pre n_pre total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = (n_pre + 0 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + 0 ) vals_l )
  **  (IntArray.undef_seg vals_pre (n_pre + 0 ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (vals_l_2)) = n_pre)) (PreH9 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth k_3 vals_l_2 0) = (Znth k_3 beads_l 0)))) (PreH10 : (EnergyLabelsBounded beads_l n_pre )) (PreH11 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg vals_pre 0 n_pre vals_l_2 )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = (n_pre + 0 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.seg vals_pre 0 (n_pre + 0 ) vals_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
).

Definition energyNecklace_entail_wit_6 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg vals_pre 0 ((n_pre + i ) + 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg vals_pre ((n_pre + i ) + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = (n_pre + (i + 1 ) )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + (i + 1 ) ) vals_l )
  **  (IntArray.undef_seg vals_pre (n_pre + (i + 1 ) ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg vals_pre 0 ((n_pre + i ) + 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = (n_pre + (i + 1 ) )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.seg vals_pre 0 (n_pre + (i + 1 ) ) vals_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
).

Definition energyNecklace_entail_wit_7 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + i ) vals_l_2 )
  **  (IntArray.undef_seg vals_pre (n_pre + i ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
) \/
(
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre ) ”
  &&  (IntArray.undef_full dp_pre (total * width ) )
).

Definition energyNecklace_entail_wit_7_split_goal_1 := 
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre ) ”
.

Definition energyNecklace_entail_wit_7_split_goal_spatial := 
forall (dp_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.undef_full dp_pre (total * width ) )
|--
  (IntArray.undef_full dp_pre (total * width ) )
.

Definition energyNecklace_entail_wit_8 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH9 : (EnergyLabelsBounded beads_l n_pre )) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (total * width )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth k dp_l 0) = 0)) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.seg dp_pre 0 0 dp_l )
  **  (IntArray.undef_seg dp_pre 0 (total * width ) )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH9 : (EnergyLabelsBounded beads_l n_pre )) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition energyNecklace_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH9 : (EnergyLabelsBounded beads_l n_pre )) (PreH10 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition energyNecklace_entail_wit_9 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.seg dp_pre 0 (i + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) (total * width ) )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (total * width )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth k dp_l 0) = 0)) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) (total * width ) )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (((Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) = 0) /\ ((Znth ((i + 1 ) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) = 0)) ” 
  &&  “ ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (((Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) = 0) /\ ((Znth ((i + 1 ) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) = 0))
.

Definition energyNecklace_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition energyNecklace_entail_wit_10 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.seg dp_pre 0 i dp_l_2 )
  **  (IntArray.undef_seg dp_pre i (total * width ) )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyZeroTable dp_l total width ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width 2 ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyLenDone vals_l_2 dp_l_2 total width 2 ) ” 
  &&  “ (EnergyZeroTable dp_l_2 total width ) ” 
  &&  “ ((Zlength (dp_l_2)) = (total * width )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyLenDone vals_l_2 dp_l_2 total width 2 )
.

Definition energyNecklace_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyZeroTable dp_l_2 total width )
.

Definition energyNecklace_entail_wit_10_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((Zlength (dp_l_2)) = (total * width ))
.

Definition energyNecklace_entail_wit_11 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width ))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH10 : (EnergyZeroTable dp_l_2 total width )) (PreH11 : (EnergyLenDone vals_l_2 dp_l_2 total width 2 )) (PreH12 : (EnergyLabelsBounded beads_l n_pre )) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width 2 ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
.

Definition energyNecklace_entail_wit_12 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (total - len )) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLeftProgress vals_l dp_l total width len 0 ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyLeftProgress vals_l_2 dp_l_2 total width len 0 ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_12_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyLeftProgress vals_l_2 dp_l_2 total width len 0 )
.

Definition energyNecklace_entail_wit_13 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (((left + len ) - 1 ) = ((left + len ) - 1 )) ” 
  &&  “ (left < ((left + len ) - 1 )) ” 
  &&  “ (0 <= ((left + len ) - 1 )) ” 
  &&  “ (((left + len ) - 1 ) < total) ” 
  &&  “ ((((left + len ) - 1 ) + 1 ) < total) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left left 0 ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergySplitProgress vals_l_2 dp_l_2 total width len left left 0 ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergySplitProgress vals_l_2 dp_l_2 total width len left left 0 )
.

Definition energyNecklace_entail_wit_14 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left < right)) (PreH13 : (0 <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1 ) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width ))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (left <= left) ” 
  &&  “ (left <= right) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left left best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left < right)) (PreH13 : (0 <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1 ) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width ))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (best <= 2100000000) ” 
  &&  “ (0 <= best) ”
  &&  emp
).

Definition energyNecklace_entail_wit_14_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left < right)) (PreH13 : (0 <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1 ) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width ))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (best <= 2100000000)
.

Definition energyNecklace_entail_wit_14_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left < right)) (PreH13 : (0 <= right)) (PreH14 : (right < total)) (PreH15 : ((right + 1 ) < total)) (PreH16 : ((Zlength (beads_l)) = n_pre)) (PreH17 : ((Zlength (dp_l_2)) = (total * width ))) (PreH18 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH19 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left left best )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (0 <= best)
.

Definition energyNecklace_entail_wit_15 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + split )) ” 
  &&  “ (((left * width ) + split ) < (total * width )) ” 
  &&  “ (0 <= (((split + 1 ) * width ) + right )) ” 
  &&  “ ((((split + 1 ) * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < total) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < total) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left split best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ ((((split + 1 ) * width ) + right ) < (total * width )) ” 
  &&  “ (((left * width ) + split ) < (total * width )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_15_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((((split + 1 ) * width ) + right ) < (total * width ))
.

Definition energyNecklace_entail_wit_15_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (((left * width ) + split ) < (total * width ))
.

Definition energyNecklace_entail_wit_16 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  EX (vals_l_2: (@list Z))  (dp_l_2: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ ((Znth ((left * width ) + split ) dp_l 0) = (Znth ((left * width ) + split ) dp_l_2 0)) ” 
  &&  “ ((Znth (((split + 1 ) * width ) + right ) dp_l 0) = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0)) ” 
  &&  “ ((((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) )) ” 
  &&  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) = (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ” 
  &&  “ (0 <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ” 
  &&  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= 2100000000) ” 
  &&  “ (0 <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= 2100000000)
.

Definition energyNecklace_entail_wit_16_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (0 <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ))
.

Definition energyNecklace_entail_wit_17_1 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH28 : (EnergyLabelsBounded beads_l n_pre )) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (left_value = (Znth ((left * width ) + split ) dp_l 0)) ” 
  &&  “ (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l 0)) ” 
  &&  “ (gain = (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ” 
  &&  “ (candidate = ((left_value + right_value ) + gain )) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 2100000000) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left (split + 1 ) best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH28 : (EnergyLabelsBounded beads_l n_pre )) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergySplitProgress vals_l_2 dp_l_2 total width len left (split + 1 ) best ) ” 
  &&  “ (best <= 2100000000) ”
  &&  emp
).

Definition energyNecklace_entail_wit_17_1_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH28 : (EnergyLabelsBounded beads_l n_pre )) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergySplitProgress vals_l_2 dp_l_2 total width len left (split + 1 ) best )
.

Definition energyNecklace_entail_wit_17_1_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH28 : (EnergyLabelsBounded beads_l n_pre )) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (best <= 2100000000)
.

Definition energyNecklace_entail_wit_17_2 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH28 : (EnergyLabelsBounded beads_l n_pre )) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (left_value = (Znth ((left * width ) + split ) dp_l 0)) ” 
  &&  “ (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l 0)) ” 
  &&  “ (gain = (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ” 
  &&  “ (candidate = ((left_value + right_value ) + gain )) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 2100000000) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left (split + 1 ) candidate ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH28 : (EnergyLabelsBounded beads_l n_pre )) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergySplitProgress vals_l_2 dp_l_2 total width len left (split + 1 ) candidate ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_17_2_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH28 : (EnergyLabelsBounded beads_l n_pre )) (PreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergySplitProgress vals_l_2 dp_l_2 total width len left (split + 1 ) candidate )
.

Definition energyNecklace_entail_wit_18 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1 ) < total)) (PreH15 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH16 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH17 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH18 : (candidate = ((left_value + right_value ) + gain ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : (0 <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width ))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH26 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left (split + 1 ) best )) (PreH27 : (EnergyLabelsBounded beads_l n_pre )) (PreH28 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= right) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left (split + 1 ) best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
.

Definition energyNecklace_entail_wit_19 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + right )) ” 
  &&  “ (((left * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left right best ) ” 
  &&  “ (EnergyIntervalBest vals_l left right best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyIntervalBest vals_l_2 left right best ) ” 
  &&  “ (EnergySplitProgress vals_l_2 dp_l_2 total width len left right best ) ” 
  &&  “ (((left * width ) + right ) < (total * width )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_19_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyIntervalBest vals_l_2 left right best )
.

Definition energyNecklace_entail_wit_19_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergySplitProgress vals_l_2 dp_l_2 total width len left right best )
.

Definition energyNecklace_entail_wit_19_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) (PreH25 : (EnergyLabelsBounded beads_l n_pre )) (PreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (((left * width ) + right ) < (total * width ))
.

Definition energyNecklace_entail_wit_20 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (EnergySplitProgress vals_l_2 dp_l total width len left right best )) (PreH21 : (EnergyIntervalBest vals_l_2 left right best )) (PreH22 : (EnergyLabelsBounded beads_l n_pre )) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full dp_pre (total * width ) (replace_Znth (((left * width ) + right )) (best) (dp_l)) )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_new: (@list Z))  (dp_old: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_old)) = (total * width )) ” 
  &&  “ ((Zlength (dp_new)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyUpdatedCell vals_l dp_old dp_new width left right best ) ” 
  &&  “ (EnergyLeftProgress vals_l dp_new total width len (left + 1 ) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_new )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (EnergySplitProgress vals_l_2 dp_l total width len left right best )) (PreH21 : (EnergyIntervalBest vals_l_2 left right best )) (PreH22 : (EnergyLabelsBounded beads_l n_pre )) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  EX (dp_old: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_old)) = (total * width )) ” 
  &&  “ ((Zlength ((replace_Znth (((left * width ) + right )) (best) (dp_l)))) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre ) ” 
  &&  “ (EnergyUpdatedCell vals_l_2 dp_old (replace_Znth (((left * width ) + right )) (best) (dp_l)) width left right best ) ” 
  &&  “ (EnergyLeftProgress vals_l_2 (replace_Znth (((left * width ) + right )) (best) (dp_l)) total width len (left + 1 ) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_21 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_old: (@list Z)) (dp_new: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (0 <= best)) (PreH13 : (best <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_old)) = (total * width ))) (PreH16 : ((Zlength (dp_new)) = (total * width ))) (PreH17 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH18 : (EnergyUpdatedCell vals_l_2 dp_old dp_new width left right best )) (PreH19 : (EnergyLeftProgress vals_l_2 dp_new total width len (left + 1 ) )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_new )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ ((left + 1 ) <= (total - len )) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLeftProgress vals_l dp_l total width len (left + 1 ) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
.

Definition energyNecklace_entail_wit_22 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (len + 1 ) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyLenDone vals_l_2 dp_l_2 total width (len + 1 ) ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_22_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) (PreH16 : (EnergyLabelsBounded beads_l n_pre )) (PreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyLenDone vals_l_2 dp_l_2 total width (len + 1 ) )
.

Definition energyNecklace_entail_wit_23 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (total * width ))) (PreH11 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH12 : (EnergyLenDone vals_l_2 dp_l_2 total width (len + 1 ) )) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= (len + 1 )) ” 
  &&  “ ((len + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (len + 1 ) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
.

Definition energyNecklace_entail_wit_24 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width 0 0 ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 0 ) ” 
  &&  “ (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_24_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 0 )
.

Definition energyNecklace_entail_wit_24_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )
.

Definition energyNecklace_entail_wit_25 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width ))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 answer )) (PreH12 : (EnergyLabelsBounded beads_l n_pre )) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width 0 answer ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width ))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 answer )) (PreH12 : (EnergyLabelsBounded beads_l n_pre )) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (answer <= 2100000000) ” 
  &&  “ (0 <= answer) ”
  &&  emp
).

Definition energyNecklace_entail_wit_25_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width ))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 answer )) (PreH12 : (EnergyLabelsBounded beads_l n_pre )) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (answer <= 2100000000)
.

Definition energyNecklace_entail_wit_25_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l_2)) = (total * width ))) (PreH9 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH10 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH11 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width 0 answer )) (PreH12 : (EnergyLabelsBounded beads_l n_pre )) (PreH13 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (0 <= answer)
.

Definition energyNecklace_entail_wit_26 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n_pre) ” 
  &&  “ (0 <= ((((start * width ) + start ) + n_pre ) - 1 )) ” 
  &&  “ (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width )) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0) ) ” 
  &&  “ (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_26_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0) )
.

Definition energyNecklace_entail_wit_26_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))
.

Definition energyNecklace_entail_wit_27 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l_2: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n_pre) ” 
  &&  “ ((Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0)) ” 
  &&  “ (0 <= (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0)) ” 
  &&  “ ((Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l_2)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l_2 total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l_2 n_pre total width start answer ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ ((Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) <= 2100000000) ” 
  &&  “ (0 <= (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0)) ”
  &&  emp
).

Definition energyNecklace_entail_wit_27_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  ((Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) <= 2100000000)
.

Definition energyNecklace_entail_wit_27_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (0 <= (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0))
.

Definition energyNecklace_entail_wit_28_1 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyLabelsBounded beads_l n_pre )) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n_pre) ” 
  &&  “ (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0)) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 2100000000) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) value ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1 ) answer ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyLabelsBounded beads_l n_pre )) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (start + 1 ) answer ) ” 
  &&  “ (answer <= 2100000000) ”
  &&  emp
).

Definition energyNecklace_entail_wit_28_1_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyLabelsBounded beads_l n_pre )) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (start + 1 ) answer )
.

Definition energyNecklace_entail_wit_28_1_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyLabelsBounded beads_l n_pre )) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (answer <= 2100000000)
.

Definition energyNecklace_entail_wit_28_2 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyLabelsBounded beads_l n_pre )) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n_pre) ” 
  &&  “ (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0)) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 2100000000) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) value ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1 ) value ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyLabelsBounded beads_l n_pre )) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (start + 1 ) value ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_28_2_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyLabelsBounded beads_l n_pre )) (PreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (start + 1 ) value )
.

Definition energyNecklace_entail_wit_29 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH10 : (0 <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width ))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH17 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH19 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width (start + 1 ) answer )) (PreH20 : (EnergyLabelsBounded beads_l n_pre )) (PreH21 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= (start + 1 )) ” 
  &&  “ ((start + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width (start + 1 ) answer ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
.

Definition energyNecklace_entail_wit_30 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyNecklaceAnswer beads_l n_pre answer ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  TT && emp 
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_30_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (EnergyNecklaceAnswer beads_l n_pre answer )
.

Definition energyNecklace_return_wit_1 := 
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= answer)) (PreH8 : (answer <= 2100000000)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (total * width ))) (PreH11 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH12 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH13 : (EnergyNecklaceAnswer beads_l n_pre answer )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (dp_l: (@list Z))  (vals_l: (@list Z)) ,
  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l (2 * n_pre ) (2 * n_pre ) (n_pre + 1 ) ) ” 
  &&  “ (EnergyNecklaceAnswer beads_l n_pre answer ) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre (2 * n_pre ) vals_l )
  **  (IntArray.full dp_pre ((2 * n_pre ) * (2 * n_pre ) ) dp_l )
) \/
(
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= answer)) (PreH8 : (answer <= 2100000000)) (PreH9 : ((Zlength (beads_l)) = n_pre)) (PreH10 : ((Zlength (dp_l_2)) = (total * width ))) (PreH11 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH12 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) (PreH13 : (EnergyNecklaceAnswer beads_l n_pre answer )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l_2 )
  **  (IntArray.full dp_pre (total * width ) dp_l_2 )
|--
  EX (dp_l: (@list Z))  (vals_l: (@list Z)) ,
  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l (2 * n_pre ) (2 * n_pre ) (n_pre + 1 ) ) ” 
  &&  “ (EnergyNecklaceAnswer beads_l n_pre answer ) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ”
  &&  (IntArray.full vals_pre (2 * n_pre ) vals_l )
  **  (IntArray.full dp_pre ((2 * n_pre ) * (2 * n_pre ) ) dp_l )
).

Definition energyNecklace_partial_solve_wit_1 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 i vals_l )
  **  (IntArray.undef_seg vals_pre i total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (i < n_pre) ” 
  &&  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int  |-> (Znth i beads_l 0))
  **  (IntArray.missing_i beads_pre i 0 n_pre beads_l )
  **  (IntArray.seg vals_pre 0 i vals_l )
  **  (IntArray.undef_seg vals_pre i total )
  **  (IntArray.undef_full dp_pre (total * width ) )
.

Definition energyNecklace_partial_solve_wit_2 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH13 : (EnergyLabelsBounded beads_l n_pre )) (PreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 i vals_l )
  **  (IntArray.undef_seg vals_pre i total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (i < n_pre) ” 
  &&  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((vals_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg vals_pre (i + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 i vals_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
.

Definition energyNecklace_partial_solve_wit_3 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg vals_pre (n_pre + i ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (i < n_pre) ” 
  &&  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = (n_pre + i )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int  |-> (Znth i beads_l 0))
  **  (IntArray.missing_i beads_pre i 0 n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg vals_pre (n_pre + i ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
.

Definition energyNecklace_partial_solve_wit_4 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0)))) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0)))) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg vals_pre (n_pre + i ) total )
  **  (IntArray.undef_full dp_pre (total * width ) )
|--
  “ (i < n_pre) ” 
  &&  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = (n_pre + i )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l 0) = (Znth k beads_l 0))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l 0) = (Znth k_2 beads_l 0))) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((vals_pre + ((n_pre + i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg vals_pre ((n_pre + i ) + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg vals_pre 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_full dp_pre (total * width ) )
.

Definition energyNecklace_partial_solve_wit_5 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l 0) = 0))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLabelsBounded beads_l n_pre )) (PreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.seg dp_pre 0 i dp_l )
  **  (IntArray.undef_seg dp_pre i (total * width ) )
|--
  “ (i < (total * width )) ” 
  &&  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (total * width )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l 0) = 0)) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (i + 1 ) (total * width ) )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.seg dp_pre 0 i dp_l )
.

Definition energyNecklace_partial_solve_wit_6 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + split )) ” 
  &&  “ (((left * width ) + split ) < (total * width )) ” 
  &&  “ (0 <= (((split + 1 ) * width ) + right )) ” 
  &&  “ ((((split + 1 ) * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < total) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < total) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left split best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((dp_pre + (((left * width ) + split ) * sizeof(INT)))) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  (IntArray.missing_i dp_pre ((left * width ) + split ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
.

Definition energyNecklace_partial_solve_wit_7 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + split )) ” 
  &&  “ (((left * width ) + split ) < (total * width )) ” 
  &&  “ (0 <= (((split + 1 ) * width ) + right )) ” 
  &&  “ ((((split + 1 ) * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < total) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < total) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left split best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((dp_pre + ((((split + 1 ) * width ) + right ) * sizeof(INT)))) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  (IntArray.missing_i dp_pre (((split + 1 ) * width ) + right ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
.

Definition energyNecklace_partial_solve_wit_8 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + split )) ” 
  &&  “ (((left * width ) + split ) < (total * width )) ” 
  &&  “ (0 <= (((split + 1 ) * width ) + right )) ” 
  &&  “ ((((split + 1 ) * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < total) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < total) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left split best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((vals_pre + (left * sizeof(INT)))) # Int  |-> (Znth left vals_l 0))
  **  (IntArray.missing_i vals_pre left 0 total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
.

Definition energyNecklace_partial_solve_wit_9 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + split )) ” 
  &&  “ (((left * width ) + split ) < (total * width )) ” 
  &&  “ (0 <= (((split + 1 ) * width ) + right )) ” 
  &&  “ ((((split + 1 ) * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < total) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < total) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left split best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((vals_pre + ((split + 1 ) * sizeof(INT)))) # Int  |-> (Znth (split + 1 ) vals_l 0))
  **  (IntArray.missing_i vals_pre (split + 1 ) 0 total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
.

Definition energyNecklace_partial_solve_wit_10 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) (PreH31 : (EnergyLabelsBounded beads_l n_pre )) (PreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ (left <= split) ” 
  &&  “ (split < right) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right < total) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + split )) ” 
  &&  “ (((left * width ) + split ) < (total * width )) ” 
  &&  “ (0 <= (((split + 1 ) * width ) + right )) ” 
  &&  “ ((((split + 1 ) * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < total) ” 
  &&  “ (0 <= (split + 1 )) ” 
  &&  “ ((split + 1 ) < total) ” 
  &&  “ (0 <= (right + 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left split best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((vals_pre + ((right + 1 ) * sizeof(INT)))) # Int  |-> (Znth (right + 1 ) vals_l 0))
  **  (IntArray.missing_i vals_pre (right + 1 ) 0 total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
.

Definition energyNecklace_partial_solve_wit_11 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH20 : (EnergySplitProgress vals_l dp_l total width len left right best )) (PreH21 : (EnergyIntervalBest vals_l left right best )) (PreH22 : (EnergyLabelsBounded beads_l n_pre )) (PreH23 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= n_pre) ” 
  &&  “ (0 <= left) ” 
  &&  “ (left < (total - len )) ” 
  &&  “ (right = ((left + len ) - 1 )) ” 
  &&  “ ((right + 1 ) < total) ” 
  &&  “ (0 <= ((left * width ) + right )) ” 
  &&  “ (((left * width ) + right ) < (total * width )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergySplitProgress vals_l dp_l total width len left right best ) ” 
  &&  “ (EnergyIntervalBest vals_l left right best ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((dp_pre + (((left * width ) + right ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_pre ((left * width ) + right ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
.

Definition energyNecklace_partial_solve_wit_12 := 
forall (dp_pre: Z) (vals_pre: Z) (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) )) (PreH15 : (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer )) (PreH16 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH17 : (EnergyLabelsBounded beads_l n_pre )) (PreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
  **  (IntArray.full dp_pre (total * width ) dp_l )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n_pre) ” 
  &&  “ (0 <= ((((start * width ) + start ) + n_pre ) - 1 )) ” 
  &&  “ (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width )) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (EnergyLenDone vals_l dp_l total width (n_pre + 1 ) ) ” 
  &&  “ (EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start answer ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) ) ” 
  &&  “ (EnergyLabelsBounded beads_l n_pre ) ” 
  &&  “ (EnergyComputationBounded beads_l n_pre 2100000000 ) ”
  &&  (((dp_pre + (((((start * width ) + start ) + n_pre ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0))
  **  (IntArray.missing_i dp_pre ((((start * width ) + start ) + n_pre ) - 1 ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full vals_pre total vals_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_energyNecklace_safety_wit_1 : energyNecklace_safety_wit_1.
Axiom proof_of_energyNecklace_safety_wit_2 : energyNecklace_safety_wit_2.
Axiom proof_of_energyNecklace_safety_wit_3 : energyNecklace_safety_wit_3.
Axiom proof_of_energyNecklace_safety_wit_4 : energyNecklace_safety_wit_4.
Axiom proof_of_energyNecklace_safety_wit_5 : energyNecklace_safety_wit_5.
Axiom proof_of_energyNecklace_safety_wit_6 : energyNecklace_safety_wit_6.
Axiom proof_of_energyNecklace_safety_wit_7 : energyNecklace_safety_wit_7.
Axiom proof_of_energyNecklace_safety_wit_8 : energyNecklace_safety_wit_8.
Axiom proof_of_energyNecklace_safety_wit_9 : energyNecklace_safety_wit_9.
Axiom proof_of_energyNecklace_safety_wit_10 : energyNecklace_safety_wit_10.
Axiom proof_of_energyNecklace_safety_wit_11 : energyNecklace_safety_wit_11.
Axiom proof_of_energyNecklace_safety_wit_12 : energyNecklace_safety_wit_12.
Axiom proof_of_energyNecklace_safety_wit_13 : energyNecklace_safety_wit_13.
Axiom proof_of_energyNecklace_safety_wit_14 : energyNecklace_safety_wit_14.
Axiom proof_of_energyNecklace_safety_wit_15 : energyNecklace_safety_wit_15.
Axiom proof_of_energyNecklace_safety_wit_16 : energyNecklace_safety_wit_16.
Axiom proof_of_energyNecklace_safety_wit_17 : energyNecklace_safety_wit_17.
Axiom proof_of_energyNecklace_safety_wit_18 : energyNecklace_safety_wit_18.
Axiom proof_of_energyNecklace_safety_wit_19 : energyNecklace_safety_wit_19.
Axiom proof_of_energyNecklace_safety_wit_20 : energyNecklace_safety_wit_20.
Axiom proof_of_energyNecklace_safety_wit_21 : energyNecklace_safety_wit_21.
Axiom proof_of_energyNecklace_safety_wit_22 : energyNecklace_safety_wit_22.
Axiom proof_of_energyNecklace_safety_wit_23 : energyNecklace_safety_wit_23.
Axiom proof_of_energyNecklace_safety_wit_24 : energyNecklace_safety_wit_24.
Axiom proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25.
Axiom proof_of_energyNecklace_safety_wit_26 : energyNecklace_safety_wit_26.
Axiom proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27.
Axiom proof_of_energyNecklace_safety_wit_28 : energyNecklace_safety_wit_28.
Axiom proof_of_energyNecklace_safety_wit_29 : energyNecklace_safety_wit_29.
Axiom proof_of_energyNecklace_safety_wit_30 : energyNecklace_safety_wit_30.
Axiom proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31.
Axiom proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32.
Axiom proof_of_energyNecklace_safety_wit_33 : energyNecklace_safety_wit_33.
Axiom proof_of_energyNecklace_safety_wit_34 : energyNecklace_safety_wit_34.
Axiom proof_of_energyNecklace_safety_wit_35 : energyNecklace_safety_wit_35.
Axiom proof_of_energyNecklace_safety_wit_36 : energyNecklace_safety_wit_36.
Axiom proof_of_energyNecklace_safety_wit_37 : energyNecklace_safety_wit_37.
Axiom proof_of_energyNecklace_safety_wit_38 : energyNecklace_safety_wit_38.
Axiom proof_of_energyNecklace_safety_wit_39 : energyNecklace_safety_wit_39.
Axiom proof_of_energyNecklace_safety_wit_40 : energyNecklace_safety_wit_40.
Axiom proof_of_energyNecklace_safety_wit_41 : energyNecklace_safety_wit_41.
Axiom proof_of_energyNecklace_safety_wit_42 : energyNecklace_safety_wit_42.
Axiom proof_of_energyNecklace_safety_wit_43 : energyNecklace_safety_wit_43.
Axiom proof_of_energyNecklace_safety_wit_44 : energyNecklace_safety_wit_44.
Axiom proof_of_energyNecklace_safety_wit_45 : energyNecklace_safety_wit_45.
Axiom proof_of_energyNecklace_entail_wit_1 : energyNecklace_entail_wit_1.
Axiom proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2.
Axiom proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3.
Axiom proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4.
Axiom proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5.
Axiom proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6.
Axiom proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7.
Axiom proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8.
Axiom proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9.
Axiom proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10.
Axiom proof_of_energyNecklace_entail_wit_11 : energyNecklace_entail_wit_11.
Axiom proof_of_energyNecklace_entail_wit_12 : energyNecklace_entail_wit_12.
Axiom proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13.
Axiom proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14.
Axiom proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15.
Axiom proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16.
Axiom proof_of_energyNecklace_entail_wit_17_1 : energyNecklace_entail_wit_17_1.
Axiom proof_of_energyNecklace_entail_wit_17_2 : energyNecklace_entail_wit_17_2.
Axiom proof_of_energyNecklace_entail_wit_18 : energyNecklace_entail_wit_18.
Axiom proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19.
Axiom proof_of_energyNecklace_entail_wit_20 : energyNecklace_entail_wit_20.
Axiom proof_of_energyNecklace_entail_wit_21 : energyNecklace_entail_wit_21.
Axiom proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22.
Axiom proof_of_energyNecklace_entail_wit_23 : energyNecklace_entail_wit_23.
Axiom proof_of_energyNecklace_entail_wit_24 : energyNecklace_entail_wit_24.
Axiom proof_of_energyNecklace_entail_wit_25 : energyNecklace_entail_wit_25.
Axiom proof_of_energyNecklace_entail_wit_26 : energyNecklace_entail_wit_26.
Axiom proof_of_energyNecklace_entail_wit_27 : energyNecklace_entail_wit_27.
Axiom proof_of_energyNecklace_entail_wit_28_1 : energyNecklace_entail_wit_28_1.
Axiom proof_of_energyNecklace_entail_wit_28_2 : energyNecklace_entail_wit_28_2.
Axiom proof_of_energyNecklace_entail_wit_29 : energyNecklace_entail_wit_29.
Axiom proof_of_energyNecklace_entail_wit_30 : energyNecklace_entail_wit_30.
Axiom proof_of_energyNecklace_return_wit_1 : energyNecklace_return_wit_1.
Axiom proof_of_energyNecklace_partial_solve_wit_1 : energyNecklace_partial_solve_wit_1.
Axiom proof_of_energyNecklace_partial_solve_wit_2 : energyNecklace_partial_solve_wit_2.
Axiom proof_of_energyNecklace_partial_solve_wit_3 : energyNecklace_partial_solve_wit_3.
Axiom proof_of_energyNecklace_partial_solve_wit_4 : energyNecklace_partial_solve_wit_4.
Axiom proof_of_energyNecklace_partial_solve_wit_5 : energyNecklace_partial_solve_wit_5.
Axiom proof_of_energyNecklace_partial_solve_wit_6 : energyNecklace_partial_solve_wit_6.
Axiom proof_of_energyNecklace_partial_solve_wit_7 : energyNecklace_partial_solve_wit_7.
Axiom proof_of_energyNecklace_partial_solve_wit_8 : energyNecklace_partial_solve_wit_8.
Axiom proof_of_energyNecklace_partial_solve_wit_9 : energyNecklace_partial_solve_wit_9.
Axiom proof_of_energyNecklace_partial_solve_wit_10 : energyNecklace_partial_solve_wit_10.
Axiom proof_of_energyNecklace_partial_solve_wit_11 : energyNecklace_partial_solve_wit_11.
Axiom proof_of_energyNecklace_partial_solve_wit_12 : energyNecklace_partial_solve_wit_12.

End VC_Correct.
