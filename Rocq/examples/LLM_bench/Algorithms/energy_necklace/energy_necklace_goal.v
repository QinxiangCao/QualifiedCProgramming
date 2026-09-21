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

(*----- Function energyNecklace -----*)

Definition energyNecklace_safety_wit_1 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "total" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition energyNecklace_safety_wit_2 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "total" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition energyNecklace_safety_wit_3 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "width" ) )) # Int  |-> (2 * n_pre ))
  **  ((( &( "total" ) )) # Int  |-> (2 * n_pre ))
  **  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_4 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.seg ( &( "vals" ) ) 0 (i + 1 ) (app (vals_l) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (i + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition energyNecklace_safety_wit_5 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 i vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) i total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_6 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + i ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((n_pre + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + i )) ”
.

Definition energyNecklace_safety_wit_7 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.seg ( &( "vals" ) ) 0 ((n_pre + i ) + 1 ) (app (vals_l) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "vals" ) ) ((n_pre + i ) + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition energyNecklace_safety_wit_8 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + i ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_9 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : ((Zlength (beads_l)) = n_pre)) (PreH8 : ((Zlength (dp_l)) = i)) (PreH9 : (0 <= i)) (PreH10 : (i <= (total * width ))) (PreH11 : (Forall (eq (0)) dp_l )) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 i dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) i (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((total * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total * width )) ”
.

Definition energyNecklace_safety_wit_10 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l )) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 i dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) i (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_11 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l )) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.seg ( &( "dp" ) ) 0 (i + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (i + 1 ) (total * width ) )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition energyNecklace_safety_wit_12 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l )) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 i dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) i (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition energyNecklace_safety_wit_13 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l)) = total)) (PreH16 : ((Zlength (dp_l)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_14 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left <= (total - len ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= len)) (PreH19 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH20 : (2 <= len)) (PreH21 : (0 <= left)) (PreH22 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : (Forall (Z.le (1)) beads_l )) (PreH25 : (Forall (Z.ge (1000)) beads_l )) (PreH26 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((total - len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total - len )) ”
.

Definition energyNecklace_safety_wit_15 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((left + len ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left + len ) - 1 )) ”
.

Definition energyNecklace_safety_wit_16 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((left + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + len )) ”
.

Definition energyNecklace_safety_wit_17 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_18 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "best" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> ((left + len ) - 1 ))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_19 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((left * width ) + split ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left * width ) + split )) ”
.

Definition energyNecklace_safety_wit_20 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "left_value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((left * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * width )) ”
.

Definition energyNecklace_safety_wit_21 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((split + 1 ) * width ) + right ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((split + 1 ) * width ) + right )) ”
.

Definition energyNecklace_safety_wit_22 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((split + 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((split + 1 ) * width )) ”
.

Definition energyNecklace_safety_wit_23 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition energyNecklace_safety_wit_24 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "right_value" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_25 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ”
) \/
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ”
).

Definition energyNecklace_safety_wit_25_split_goal_1 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_25_split_goal_2 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((INT_MIN) <= (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) )) ”
.

Definition energyNecklace_safety_wit_26 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((right + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right + 1 )) ”
.

Definition energyNecklace_safety_wit_27 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) )) ”
) \/
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) )) ”
).

Definition energyNecklace_safety_wit_27_split_goal_1 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_27_split_goal_2 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((INT_MIN) <= ((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) )) ”
.

Definition energyNecklace_safety_wit_28 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition energyNecklace_safety_wit_29 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_30 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |->_)
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_31 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ”
) \/
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ”
).

Definition energyNecklace_safety_wit_31_split_goal_1 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_31_split_goal_2 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((INT_MIN) <= (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ) )) ”
.

Definition energyNecklace_safety_wit_32 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) )) ”
) \/
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) )) ”
).

Definition energyNecklace_safety_wit_32_split_goal_1 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) ) <= INT_MAX) ”
.

Definition energyNecklace_safety_wit_32_split_goal_2 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "candidate" ) )) # Int  |->_)
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  ((( &( "gain" ) )) # Int  |-> (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  ((( &( "right_value" ) )) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  ((( &( "left_value" ) )) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((INT_MIN) <= ((Znth ((left * width ) + split ) dp_l 0) + (Znth (((split + 1 ) * width ) + right ) dp_l 0) )) ”
.

Definition energyNecklace_safety_wit_33 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1 ) < total)) (PreH15 : (left_value = (Znth ((left * width ) + split ) dp_l 0))) (PreH16 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l 0))) (PreH17 : (gain = (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (right + 1 ) vals_l 0) ))) (PreH18 : (candidate = ((left_value + right_value ) + gain ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : (0 <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l)) = (total * width ))) (PreH25 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH26 : (0 <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l)) = total)) (PreH29 : ((Zlength (dp_l)) = (total * width ))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH32 : (2 <= len)) (PreH33 : (0 <= left)) (PreH34 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH35 : ((left + len ) <= total)) (PreH36 : (left <= (split + 1 ))) (PreH37 : ((split + 1 ) <= ((left + len ) - 1 ))) (PreH38 : (0 <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l dp_l width len left (split + 1 ) best )) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall (Z.le (1)) beads_l )) (PreH43 : (Forall (Z.ge (1000)) beads_l )) (PreH44 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "split" ) )) # Int  |-> split)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((split + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (split + 1 )) ”
.

Definition energyNecklace_safety_wit_34 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best )) (PreH35 : (EnergyIntervalBest vals_l left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((left * width ) + right ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left * width ) + right )) ”
.

Definition energyNecklace_safety_wit_35 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best )) (PreH35 : (EnergyIntervalBest vals_l left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((left * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left * width )) ”
.

Definition energyNecklace_safety_wit_36 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best )) (PreH35 : (EnergyIntervalBest vals_l left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "dp" ) ) (total * width ) (replace_Znth (((left * width ) + right )) (best) (dp_l)) )
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((left + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left + 1 )) ”
.

Definition energyNecklace_safety_wit_37 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((len + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + 1 )) ”
.

Definition energyNecklace_safety_wit_38 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l)) = total)) (PreH16 : ((Zlength (dp_l)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_39 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l)) = total)) (PreH16 : ((Zlength (dp_l)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |-> 0)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition energyNecklace_safety_wit_40 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((((start * width ) + start ) + n_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((start * width ) + start ) + n_pre ) - 1 )) ”
.

Definition energyNecklace_safety_wit_41 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((((start * width ) + start ) + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((start * width ) + start ) + n_pre )) ”
.

Definition energyNecklace_safety_wit_42 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (((start * width ) + start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((start * width ) + start )) ”
.

Definition energyNecklace_safety_wit_43 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((start * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start * width )) ”
.

Definition energyNecklace_safety_wit_44 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start_2: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (0 <= ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ))) (PreH10 : (((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start_2)) (PreH24 : (start_2 <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start_2 answer )) (PreH28 : (EnergyIntervalBest vals_l start_2 ((start_2 + n_pre ) - 1 ) (Znth ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start_2)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition energyNecklace_safety_wit_45 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0))) (PreH10 : (0 <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l)) = (total * width ))) (PreH16 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH17 : (0 <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l)) = total)) (PreH20 : ((Zlength (dp_l)) = (total * width ))) (PreH21 : (1 <= (n_pre + 1 ))) (PreH22 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH23 : (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) value )) (PreH24 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH25 : ((Zlength (dp_l)) = (total * width ))) (PreH26 : (width = total)) (PreH27 : (0 <= (start + 1 ))) (PreH28 : ((start + 1 ) <= n_pre)) (PreH29 : (0 <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l n_pre (start + 1 ) answer )) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall (Z.le (1)) beads_l )) (PreH34 : (Forall (Z.ge (1000)) beads_l )) (PreH35 : forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "beads" ) )) # Ptr  |-> beads_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ ((start + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + 1 )) ”
.

Definition energyNecklace_entail_wit_1 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
  **  (IntArray.full beads_pre n_pre beads_l )
|--
  EX (vals_l: (@list Z)) ,
  “ ((2 * n_pre ) = (2 * n_pre )) ” 
  &&  “ ((2 * n_pre ) = (2 * n_pre )) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= (2 * n_pre )) ” 
  &&  “ ((2 * n_pre ) <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (vals_l)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (Forall2 eq (sublist (0) (0) (vals_l)) (sublist (0) (0) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 0 vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) 0 (2 * n_pre ) )
  **  (IntArray.undef_full ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (Forall2 eq (sublist (0) (0) ((@nil Z))) (sublist (0) (0) (beads_l)) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (IntArray.undef_seg ( &( "vals" ) ) 0 (2 * n_pre ) )
  **  (IntArray.undef_full ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
).

Definition energyNecklace_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
.

Definition energyNecklace_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
|--
  “ (Forall2 eq (sublist (0) (0) ((@nil Z))) (sublist (0) (0) (beads_l)) ) ”
.

Definition energyNecklace_entail_wit_1_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition energyNecklace_entail_wit_1_split_goal_spatial := 
forall (n_pre: Z) (beads_l: (@list Z)) (PreH1 : (4 <= n_pre)) (PreH2 : (n_pre <= 100)) (PreH3 : ((Zlength (beads_l)) = n_pre)) (PreH4 : ((Zlength (beads_l)) = n_pre)) (PreH5 : (Forall (Z.le (1)) beads_l )) (PreH6 : (Forall (Z.ge (1000)) beads_l )) (PreH7 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
|--
  (IntArray.undef_seg ( &( "vals" ) ) 0 (2 * n_pre ) )
  **  (IntArray.undef_full ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_entail_wit_2 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.seg ( &( "vals" ) ) 0 (i + 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (i + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall2 eq (sublist (0) ((i + 1 )) (vals_l)) (sublist (0) ((i + 1 )) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (i + 1 ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (i + 1 ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  TT && emp 
|--
  “ (Forall2 eq (sublist (0) ((i + 1 )) ((app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))))) (sublist (0) ((i + 1 )) (beads_l)) ) ” 
  &&  “ ((Zlength ((app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (Forall2 eq (sublist (0) ((i + 1 )) ((app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))))) (sublist (0) ((i + 1 )) (beads_l)) )
.

Definition energyNecklace_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((Zlength ((app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))))) = (i + 1 ))
.

Definition energyNecklace_entail_wit_3 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 i vals_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) i total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) ) ” 
  &&  “ (Forall2 eq (sublist (n_pre) ((n_pre + 0 )) (vals_l)) (sublist (0) (0) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + 0 ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + 0 ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.seg ( &( "vals" ) ) 0 i vals_l_2 )
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
  &&  “ (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) ) ” 
  &&  “ (Forall2 eq (sublist (n_pre) ((n_pre + 0 )) (vals_l)) (sublist (0) (0) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + 0 ) vals_l )
).

Definition energyNecklace_entail_wit_4 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l_2)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.seg ( &( "vals" ) ) 0 ((n_pre + i ) + 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "vals" ) ) ((n_pre + i ) + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) ) ” 
  &&  “ (Forall2 eq (sublist (n_pre) ((n_pre + (i + 1 ) )) (vals_l)) (sublist (0) ((i + 1 )) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + (i + 1 ) ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + (i + 1 ) ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l_2)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.seg ( &( "vals" ) ) 0 ((n_pre + i ) + 1 ) (app (vals_l_2) ((cons ((Znth i beads_l 0)) ((@nil Z))))) )
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
  &&  “ (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) ) ” 
  &&  “ (Forall2 eq (sublist (n_pre) ((n_pre + (i + 1 ) )) (vals_l)) (sublist (0) ((i + 1 )) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + (i + 1 ) ) vals_l )
).

Definition energyNecklace_entail_wit_5 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l_2)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + i ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 0 dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) 0 (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l_2)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l_2)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l_2 )
|--
  EX (vals_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (total * width )) ” 
  &&  “ (Forall (eq (0)) (@nil Z) ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full ( &( "vals" ) ) total vals_l )
).

Definition energyNecklace_entail_wit_6 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l_2 )) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.seg ( &( "dp" ) ) 0 (i + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (i + 1 ) (total * width ) )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 (i + 1 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (i + 1 ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l_2 )) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  TT && emp 
|--
  “ (Forall (eq (0)) (app (dp_l_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l_2 )) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (Forall (eq (0)) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
.

Definition energyNecklace_entail_wit_6_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l_2 )) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) = (i + 1 ))
.

Definition energyNecklace_entail_wit_7 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l_2 )) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.seg ( &( "dp" ) ) 0 i dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) i (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= 2) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width 2 ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (i: Z) (dp_l_2: (@list Z)) (width: Z) (total: Z) (PreH1 : (i >= (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l_2)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l_2 )) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.seg ( &( "dp" ) ) 0 i dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
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
  &&  “ (EnergyValsDuplicated beads_l vals_l_2 n_pre ) ” 
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l_2)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= 2) ” 
  &&  “ (EnergyLengthsComplete vals_l_2 dp_l width 2 ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
).

Definition energyNecklace_entail_wit_8 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len 0 ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyLeftComplete vals_l_2 dp_l_2 width len 0 ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_8_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_8_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len <= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyLeftComplete vals_l_2 dp_l_2 width len 0 )
.

Definition energyNecklace_entail_wit_9 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (left <= left) ” 
  &&  “ (left <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= left) ” 
  &&  “ (left <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left left 0 ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergySplitBest vals_l_2 dp_l_2 width len left left 0 ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_9_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_9_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left < (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 width len left left 0 )
.

Definition energyNecklace_entail_wit_10 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left split best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ ((((split + 1 ) * width ) + ((left + len ) - 1 ) ) < ((2 * n_pre ) * width )) ” 
  &&  “ (((left * width ) + split ) < ((2 * n_pre ) * width )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_10_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_10_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  ((((split + 1 ) * width ) + ((left + len ) - 1 ) ) < ((2 * n_pre ) * width ))
.

Definition energyNecklace_entail_wit_10_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split < right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (((left * width ) + split ) < ((2 * n_pre ) * width ))
.

Definition energyNecklace_entail_wit_11 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l_2)) = total) ” 
  &&  “ ((Zlength (dp_l_2)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l_2 dp_l_2 width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l_2 dp_l_2 width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l_2 dp_l_2 width len left split best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ ((((Znth ((left * total ) + split ) dp_l 0) + (Znth (((split + 1 ) * total ) + ((left + len ) - 1 ) ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (((left + len ) - 1 ) + 1 ) vals_l 0) ) ) <= 2100000000) ” 
  &&  “ (0 <= (((Znth ((left * total ) + split ) dp_l 0) + (Znth (((split + 1 ) * total ) + ((left + len ) - 1 ) ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (((left + len ) - 1 ) + 1 ) vals_l 0) ) )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_11_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_11_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  ((((Znth ((left * total ) + split ) dp_l 0) + (Znth (((split + 1 ) * total ) + ((left + len ) - 1 ) ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (((left + len ) - 1 ) + 1 ) vals_l 0) ) ) <= 2100000000)
.

Definition energyNecklace_entail_wit_11_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (0 <= (((Znth ((left * total ) + split ) dp_l 0) + (Znth (((split + 1 ) * total ) + ((left + len ) - 1 ) ) dp_l 0) ) + (((Znth left vals_l 0) * (Znth (split + 1 ) vals_l 0) ) * (Znth (((left + len ) - 1 ) + 1 ) vals_l 0) ) ))
.

Definition energyNecklace_entail_wit_12_1 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= candidate) ” 
  &&  “ (candidate <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left (split + 1 ) candidate ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1 ) ((left_value + right_value ) + gain ) ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_12_1_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_12_1_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate > best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1 ) ((left_value + right_value ) + gain ) )
.

Definition energyNecklace_entail_wit_12_2 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left (split + 1 ) best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1 ) best ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_12_2_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_12_2_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (candidate <= best)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left <= split)) (PreH14 : (split < right)) (PreH15 : (0 <= right)) (PreH16 : (right < total)) (PreH17 : ((right + 1 ) < total)) (PreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH21 : (candidate = ((left_value + right_value ) + gain ))) (PreH22 : (0 <= candidate)) (PreH23 : (candidate <= 2100000000)) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH27 : (0 <= total)) (PreH28 : (width = total)) (PreH29 : ((Zlength (vals_l_2)) = total)) (PreH30 : ((Zlength (dp_l_2)) = (total * width ))) (PreH31 : (1 <= len)) (PreH32 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH33 : (2 <= len)) (PreH34 : (0 <= left)) (PreH35 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH36 : ((left + len ) <= total)) (PreH37 : (left <= split)) (PreH38 : (split <= ((left + len ) - 1 ))) (PreH39 : (0 <= best)) (PreH40 : (best <= 2100000000)) (PreH41 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH42 : ((Zlength (beads_l)) = n_pre)) (PreH43 : (Forall (Z.le (1)) beads_l )) (PreH44 : (Forall (Z.ge (1000)) beads_l )) (PreH45 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 total len left (split + 1 ) best )
.

Definition energyNecklace_entail_wit_13 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1 ) < total)) (PreH15 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH16 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH17 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH18 : (candidate = ((left_value + right_value ) + gain ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : (0 <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width ))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH26 : (0 <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l_2)) = total)) (PreH29 : ((Zlength (dp_l_2)) = (total * width ))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH32 : (2 <= len)) (PreH33 : (0 <= left)) (PreH34 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH35 : ((left + len ) <= total)) (PreH36 : (left <= (split + 1 ))) (PreH37 : ((split + 1 ) <= ((left + len ) - 1 ))) (PreH38 : (0 <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l_2 dp_l_2 width len left (split + 1 ) best )) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall (Z.le (1)) beads_l )) (PreH43 : (Forall (Z.ge (1000)) beads_l )) (PreH44 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= (split + 1 )) ” 
  &&  “ ((split + 1 ) <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left (split + 1 ) best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1 ) < total)) (PreH15 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH16 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH17 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH18 : (candidate = ((left_value + right_value ) + gain ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : (0 <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width ))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH26 : (0 <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l_2)) = total)) (PreH29 : ((Zlength (dp_l_2)) = (total * width ))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH32 : (2 <= len)) (PreH33 : (0 <= left)) (PreH34 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH35 : ((left + len ) <= total)) (PreH36 : (left <= (split + 1 ))) (PreH37 : ((split + 1 ) <= ((left + len ) - 1 ))) (PreH38 : (0 <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l_2 dp_l_2 width len left (split + 1 ) best )) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall (Z.le (1)) beads_l )) (PreH43 : (Forall (Z.ge (1000)) beads_l )) (PreH44 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  emp
).

Definition energyNecklace_entail_wit_13_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (left_value: Z) (right_value: Z) (gain: Z) (candidate: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : ((right + 1 ) < total)) (PreH15 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) (PreH16 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) (PreH17 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) (PreH18 : (candidate = ((left_value + right_value ) + gain ))) (PreH19 : (0 <= candidate)) (PreH20 : (candidate <= 2100000000)) (PreH21 : (0 <= best)) (PreH22 : (best <= 2100000000)) (PreH23 : ((Zlength (beads_l)) = n_pre)) (PreH24 : ((Zlength (dp_l_2)) = (total * width ))) (PreH25 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH26 : (0 <= total)) (PreH27 : (width = total)) (PreH28 : ((Zlength (vals_l_2)) = total)) (PreH29 : ((Zlength (dp_l_2)) = (total * width ))) (PreH30 : (1 <= len)) (PreH31 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH32 : (2 <= len)) (PreH33 : (0 <= left)) (PreH34 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH35 : ((left + len ) <= total)) (PreH36 : (left <= (split + 1 ))) (PreH37 : ((split + 1 ) <= ((left + len ) - 1 ))) (PreH38 : (0 <= best)) (PreH39 : (best <= 2100000000)) (PreH40 : (EnergySplitBest vals_l_2 dp_l_2 width len left (split + 1 ) best )) (PreH41 : ((Zlength (beads_l)) = n_pre)) (PreH42 : (Forall (Z.le (1)) beads_l )) (PreH43 : (Forall (Z.ge (1000)) beads_l )) (PreH44 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_14 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left right best ) ” 
  &&  “ (EnergyIntervalBest vals_l left right best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyIntervalBest vals_l_2 left ((left + len ) - 1 ) best ) ” 
  &&  “ (EnergySplitBest vals_l_2 dp_l_2 width len left ((left + len ) - 1 ) best ) ” 
  &&  “ (((left * width ) + ((left + len ) - 1 ) ) < ((2 * n_pre ) * width )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_14_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_14_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyIntervalBest vals_l_2 left ((left + len ) - 1 ) best )
.

Definition energyNecklace_entail_wit_14_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergySplitBest vals_l_2 dp_l_2 width len left ((left + len ) - 1 ) best )
.

Definition energyNecklace_entail_wit_14_split_goal_4 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (best: Z) (split: Z) (right: Z) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (split >= right)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left < (total - len ))) (PreH12 : (right = ((left + len ) - 1 ))) (PreH13 : (left < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (left <= split)) (PreH18 : (split <= right)) (PreH19 : (0 <= best)) (PreH20 : (best <= 2100000000)) (PreH21 : ((Zlength (beads_l)) = n_pre)) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH24 : (0 <= total)) (PreH25 : (width = total)) (PreH26 : ((Zlength (vals_l_2)) = total)) (PreH27 : ((Zlength (dp_l_2)) = (total * width ))) (PreH28 : (1 <= len)) (PreH29 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH30 : (2 <= len)) (PreH31 : (0 <= left)) (PreH32 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH33 : ((left + len ) <= total)) (PreH34 : (left <= split)) (PreH35 : (split <= ((left + len ) - 1 ))) (PreH36 : (0 <= best)) (PreH37 : (best <= 2100000000)) (PreH38 : (EnergySplitBest vals_l_2 dp_l_2 width len left split best )) (PreH39 : ((Zlength (beads_l)) = n_pre)) (PreH40 : (Forall (Z.le (1)) beads_l )) (PreH41 : (Forall (Z.ge (1000)) beads_l )) (PreH42 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (((left * width ) + ((left + len ) - 1 ) ) < ((2 * n_pre ) * width ))
.

Definition energyNecklace_entail_wit_15 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best )) (PreH35 : (EnergyIntervalBest vals_l_2 left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full ( &( "dp" ) ) (total * width ) (replace_Znth (((left * width ) + right )) (best) (dp_l_2)) )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= (left + 1 )) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len (left + 1 ) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best )) (PreH35 : (EnergyIntervalBest vals_l_2 left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyLeftComplete vals_l_2 (replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)) total len (left + 1 ) ) ” 
  &&  “ (EnergyLengthsComplete vals_l_2 (replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)) total len ) ” 
  &&  “ ((Zlength ((replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)))) = ((2 * n_pre ) * total )) ” 
  &&  “ ((Zlength ((replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)))) = ((2 * n_pre ) * total )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_15_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best )) (PreH35 : (EnergyIntervalBest vals_l_2 left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_15_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best )) (PreH35 : (EnergyIntervalBest vals_l_2 left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyLeftComplete vals_l_2 (replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)) total len (left + 1 ) )
.

Definition energyNecklace_entail_wit_15_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best )) (PreH35 : (EnergyIntervalBest vals_l_2 left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyLengthsComplete vals_l_2 (replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)) total len )
.

Definition energyNecklace_entail_wit_15_split_goal_4 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best )) (PreH35 : (EnergyIntervalBest vals_l_2 left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  ((Zlength ((replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)))) = ((2 * n_pre ) * total ))
.

Definition energyNecklace_entail_wit_15_split_goal_5 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l_2)) = total)) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l_2 dp_l_2 width len left right best )) (PreH35 : (EnergyIntervalBest vals_l_2 left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  ((Zlength ((replace_Znth (((left * total ) + ((left + len ) - 1 ) )) (best) (dp_l_2)))) = ((2 * n_pre ) * total ))
.

Definition energyNecklace_entail_wit_16 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= (len + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width (len + 1 ) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyLengthsComplete vals_l_2 dp_l_2 width (len + 1 ) ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_16_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_16_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (left: Z) (len: Z) (width: Z) (total: Z) (PreH1 : (left >= (total - len ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= n_pre)) (PreH10 : (0 <= left)) (PreH11 : (left <= (total - len ))) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= len)) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH21 : (2 <= len)) (PreH22 : (0 <= left)) (PreH23 : (EnergyLeftComplete vals_l_2 dp_l_2 width len left )) (PreH24 : ((Zlength (beads_l)) = n_pre)) (PreH25 : (Forall (Z.le (1)) beads_l )) (PreH26 : (Forall (Z.ge (1000)) beads_l )) (PreH27 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyLengthsComplete vals_l_2 dp_l_2 width (len + 1 ) )
.

Definition energyNecklace_entail_wit_17 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (width = total) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2100000000) ” 
  &&  “ (EnergyAnswerBest vals_l n_pre 0 0 ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyAnswerBest vals_l_2 n_pre 0 0 ) ” 
  &&  “ (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_17_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_17_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyAnswerBest vals_l_2 n_pre 0 0 )
.

Definition energyNecklace_entail_wit_17_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (len: Z) (width: Z) (total: Z) (PreH1 : (len > n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (2 <= len)) (PreH9 : (len <= (n_pre + 1 ))) (PreH10 : ((Zlength (beads_l)) = n_pre)) (PreH11 : ((Zlength (dp_l_2)) = (total * width ))) (PreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH13 : (0 <= total)) (PreH14 : (width = total)) (PreH15 : ((Zlength (vals_l_2)) = total)) (PreH16 : ((Zlength (dp_l_2)) = (total * width ))) (PreH17 : (1 <= len)) (PreH18 : (EnergyLengthsComplete vals_l_2 dp_l_2 width len )) (PreH19 : ((Zlength (beads_l)) = n_pre)) (PreH20 : (Forall (Z.le (1)) beads_l )) (PreH21 : (Forall (Z.ge (1000)) beads_l )) (PreH22 : forall (ev_2: (@list Z)) , forall (start_2: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_2 ((start_2 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )
.

Definition energyNecklace_entail_wit_18 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (width = total) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ (EnergyAnswerBest vals_l n_pre start answer ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0) ) ” 
  &&  “ (((((start * width ) + start ) + n_pre ) - 1 ) < ((2 * n_pre ) * width )) ”
  &&  emp
).

Definition energyNecklace_entail_wit_18_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_18_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0) )
.

Definition energyNecklace_entail_wit_18_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (answer: Z) (start: Z) (width: Z) (total: Z) (PreH1 : (start < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l_2)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l_2)) = total)) (PreH18 : ((Zlength (dp_l_2)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH22 : ((Zlength (dp_l_2)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start)) (PreH25 : (start <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (((((start * width ) + start ) + n_pre ) - 1 ) < ((2 * n_pre ) * width ))
.

Definition energyNecklace_entail_wit_19 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l_2)) = (total * width )) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l_2 width (n_pre + 1 ) ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (dp_l_2)) = (total * width )) ” 
  &&  “ (width = total) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ (EnergyAnswerBest vals_l n_pre start answer ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ ((Znth ((((start * total ) + start ) + n_pre ) - 1 ) dp_l 0) <= 2100000000) ” 
  &&  “ (0 <= (Znth ((((start * total ) + start ) + n_pre ) - 1 ) dp_l 0)) ”
  &&  emp
).

Definition energyNecklace_entail_wit_19_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_19_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  ((Znth ((((start * total ) + start ) + n_pre ) - 1 ) dp_l 0) <= 2100000000)
.

Definition energyNecklace_entail_wit_19_split_goal_3 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start)) (PreH8 : (start < n_pre)) (PreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) (PreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l_2)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l_2 dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start)) (PreH24 : (start <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH28 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (0 <= (Znth ((((start * total ) + start ) + n_pre ) - 1 ) dp_l 0))
.

Definition energyNecklace_entail_wit_20_1 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) value ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (width = total) ” 
  &&  “ (0 <= (start + 1 )) ” 
  &&  “ ((start + 1 ) <= n_pre) ” 
  &&  “ (0 <= value) ” 
  &&  “ (value <= 2100000000) ” 
  &&  “ (EnergyAnswerBest vals_l n_pre (start + 1 ) value ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyAnswerBest vals_l_2 n_pre (start + 1 ) value ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_20_1_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_20_1_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value > answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyAnswerBest vals_l_2 n_pre (start + 1 ) value )
.

Definition energyNecklace_entail_wit_20_2 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) ) ” 
  &&  “ (EnergyIntervalBest vals_l start ((start + n_pre ) - 1 ) value ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (width = total) ” 
  &&  “ (0 <= (start + 1 )) ” 
  &&  “ ((start + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ (EnergyAnswerBest vals_l n_pre (start + 1 ) answer ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ” 
  &&  “ (EnergyAnswerBest vals_l_2 n_pre (start + 1 ) answer ) ”
  &&  emp
).

Definition energyNecklace_entail_wit_20_2_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start_2: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start_2)) /\ (start_2 < n_pre)) /\ (EnergyIntervalPlan ev start_2 ((start_2 + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_20_2_split_goal_2 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start: Z) (value: Z) (answer: Z) (PreH1 : (value <= answer)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start)) (PreH9 : (start < n_pre)) (PreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) (PreH11 : (0 <= value)) (PreH12 : (value <= 2100000000)) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : ((Zlength (dp_l_2)) = (total * width ))) (PreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH16 : (0 <= total)) (PreH17 : (width = total)) (PreH18 : ((Zlength (vals_l_2)) = total)) (PreH19 : ((Zlength (dp_l_2)) = (total * width ))) (PreH20 : (1 <= (n_pre + 1 ))) (PreH21 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH22 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH23 : ((Zlength (dp_l_2)) = (total * width ))) (PreH24 : (width = total)) (PreH25 : (0 <= start)) (PreH26 : (start <= n_pre)) (PreH27 : (0 <= answer)) (PreH28 : (answer <= 2100000000)) (PreH29 : (EnergyAnswerBest vals_l_2 n_pre start answer )) (PreH30 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) (PreH31 : ((Zlength (beads_l)) = n_pre)) (PreH32 : (Forall (Z.le (1)) beads_l )) (PreH33 : (Forall (Z.ge (1000)) beads_l )) (PreH34 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (EnergyAnswerBest vals_l_2 n_pre (start + 1 ) answer )
.

Definition energyNecklace_entail_wit_21 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start_2: Z) (value: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (value = (Znth ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) dp_l_2 0))) (PreH10 : (0 <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width ))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH17 : (0 <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l_2)) = total)) (PreH20 : ((Zlength (dp_l_2)) = (total * width ))) (PreH21 : (1 <= (n_pre + 1 ))) (PreH22 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH23 : (EnergyIntervalBest vals_l_2 start_2 ((start_2 + n_pre ) - 1 ) value )) (PreH24 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (width = total)) (PreH27 : (0 <= (start_2 + 1 ))) (PreH28 : ((start_2 + 1 ) <= n_pre)) (PreH29 : (0 <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l_2 n_pre (start_2 + 1 ) answer )) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall (Z.le (1)) beads_l )) (PreH34 : (Forall (Z.ge (1000)) beads_l )) (PreH35 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l_2 )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  EX (vals_l: (@list Z))  (dp_l: (@list Z)) ,
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= (start_2 + 1 )) ” 
  &&  “ ((start_2 + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (width = total) ” 
  &&  “ (0 <= (start_2 + 1 )) ” 
  &&  “ ((start_2 + 1 ) <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ (EnergyAnswerBest vals_l n_pre (start_2 + 1 ) answer ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start_2: Z) (value: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (value = (Znth ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) dp_l_2 0))) (PreH10 : (0 <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width ))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH17 : (0 <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l_2)) = total)) (PreH20 : ((Zlength (dp_l_2)) = (total * width ))) (PreH21 : (1 <= (n_pre + 1 ))) (PreH22 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH23 : (EnergyIntervalBest vals_l_2 start_2 ((start_2 + n_pre ) - 1 ) value )) (PreH24 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (width = total)) (PreH27 : (0 <= (start_2 + 1 ))) (PreH28 : ((start_2 + 1 ) <= n_pre)) (PreH29 : (0 <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l_2 n_pre (start_2 + 1 ) answer )) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall (Z.le (1)) beads_l )) (PreH34 : (Forall (Z.ge (1000)) beads_l )) (PreH35 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  TT && emp 
|--
  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  emp
).

Definition energyNecklace_entail_wit_21_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l_2: (@list Z)) (dp_l_2: (@list Z)) (total: Z) (width: Z) (start_2: Z) (value: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (value = (Znth ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) dp_l_2 0))) (PreH10 : (0 <= value)) (PreH11 : (value <= 2100000000)) (PreH12 : (0 <= answer)) (PreH13 : (answer <= 2100000000)) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : ((Zlength (dp_l_2)) = (total * width ))) (PreH16 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH17 : (0 <= total)) (PreH18 : (width = total)) (PreH19 : ((Zlength (vals_l_2)) = total)) (PreH20 : ((Zlength (dp_l_2)) = (total * width ))) (PreH21 : (1 <= (n_pre + 1 ))) (PreH22 : (EnergyLengthsComplete vals_l_2 dp_l_2 width (n_pre + 1 ) )) (PreH23 : (EnergyIntervalBest vals_l_2 start_2 ((start_2 + n_pre ) - 1 ) value )) (PreH24 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) (PreH25 : ((Zlength (dp_l_2)) = (total * width ))) (PreH26 : (width = total)) (PreH27 : (0 <= (start_2 + 1 ))) (PreH28 : ((start_2 + 1 ) <= n_pre)) (PreH29 : (0 <= answer)) (PreH30 : (answer <= 2100000000)) (PreH31 : (EnergyAnswerBest vals_l_2 n_pre (start_2 + 1 ) answer )) (PreH32 : ((Zlength (beads_l)) = n_pre)) (PreH33 : (Forall (Z.le (1)) beads_l )) (PreH34 : (Forall (Z.ge (1000)) beads_l )) (PreH35 : forall (ev_2: (@list Z)) , forall (start_3: Z) , forall (energy_2: Z) , (((((EnergyValsDuplicated beads_l ev_2 n_pre ) /\ (0 <= start_3)) /\ (start_3 < n_pre)) /\ (EnergyIntervalPlan ev_2 start_3 ((start_3 + n_pre ) - 1 ) energy_2 )) -> (energy_2 <= 2100000000))) ,
  forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))
.

Definition energyNecklace_entail_wit_22 := 
(
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (answer: Z) (start_2: Z) (width: Z) (total: Z) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH22 : ((Zlength (dp_l)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "answer" ) )) # Int  |-> answer)
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_full ( &( "vals" ) ) 200 )
  **  (IntArray.undef_full ( &( "dp" ) ) 40000 )
  **  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "width" ) )) # Int  |->_)
  **  ((( &( "answer" ) )) # Int  |->_)
) \/
(
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (answer: Z) (start_2: Z) (width: Z) (total: Z) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH22 : ((Zlength (dp_l)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer ) ”
  &&  (IntArray.undef_full ( &( "vals" ) ) 200 )
  **  (IntArray.undef_full ( &( "dp" ) ) 40000 )
).

Definition energyNecklace_entail_wit_22_split_goal_1 := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (answer: Z) (start_2: Z) (width: Z) (total: Z) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH22 : ((Zlength (dp_l)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (EnergyNecklaceAnswer beads_l n_pre answer ) ”
.

Definition energyNecklace_entail_wit_22_split_goal_spatial := 
forall (n_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (answer: Z) (start_2: Z) (width: Z) (total: Z) (PreH1 : (start_2 >= n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : (0 <= start_2)) (PreH9 : (start_2 <= n_pre)) (PreH10 : (0 <= answer)) (PreH11 : (answer <= 2100000000)) (PreH12 : ((Zlength (beads_l)) = n_pre)) (PreH13 : ((Zlength (dp_l)) = (total * width ))) (PreH14 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH15 : (0 <= total)) (PreH16 : (width = total)) (PreH17 : ((Zlength (vals_l)) = total)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (1 <= (n_pre + 1 ))) (PreH20 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH21 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH22 : ((Zlength (dp_l)) = (total * width ))) (PreH23 : (width = total)) (PreH24 : (0 <= start_2)) (PreH25 : (start_2 <= n_pre)) (PreH26 : (0 <= answer)) (PreH27 : (answer <= 2100000000)) (PreH28 : (EnergyAnswerBest vals_l n_pre start_2 answer )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  (IntArray.undef_full ( &( "vals" ) ) 200 )
  **  (IntArray.undef_full ( &( "dp" ) ) 40000 )
.

Definition energyNecklace_return_wit_1 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (result: Z) (PreH1 : (EnergyNecklaceAnswer beads_l n_pre result )) ,
  (IntArray.full beads_pre n_pre beads_l )
|--
  “ (EnergyNecklaceAnswer beads_l n_pre result ) ”
  &&  (IntArray.full beads_pre n_pre beads_l )
.

Definition energyNecklace_partial_solve_wit_1 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 i vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) i total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall2 eq (sublist (0) (i) (vals_l)) (sublist (0) (i) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int  |-> (Znth i beads_l 0))
  **  (IntArray.missing_i beads_pre i 0 n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 i vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) i total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_2 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (i) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH13 : ((Zlength (beads_l)) = n_pre)) (PreH14 : (Forall (Z.le (1)) beads_l )) (PreH15 : (Forall (Z.ge (1000)) beads_l )) (PreH16 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 i vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) i total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall2 eq (sublist (0) (i) (vals_l)) (sublist (0) (i) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "vals" ) ) (i + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 i vals_l )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_3 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + i ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) ) ” 
  &&  “ (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l)) (sublist (0) (i) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((beads_pre + (i * sizeof(INT)))) # Int  |-> (Znth i beads_l 0))
  **  (IntArray.missing_i beads_pre i 0 n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + i ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_4 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (i: Z) (vals_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < n_pre)) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (vals_l)) = (n_pre + i ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) )) (PreH13 : (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l)) (sublist (0) (i) (beads_l)) )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (n_pre + i ) total )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall2 eq (sublist (0) (n_pre) (vals_l)) (sublist (0) (n_pre) (beads_l)) ) ” 
  &&  “ (Forall2 eq (sublist (n_pre) ((n_pre + i )) (vals_l)) (sublist (0) (i) (beads_l)) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + ((n_pre + i ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "vals" ) ) ((n_pre + i ) + 1 ) total )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.seg ( &( "vals" ) ) 0 (n_pre + i ) vals_l )
  **  (IntArray.undef_full ( &( "dp" ) ) (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_5 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (i: Z) (dp_l: (@list Z)) (width: Z) (total: Z) (PreH1 : (i < (total * width ))) (PreH2 : (total = (2 * n_pre ))) (PreH3 : (width = total)) (PreH4 : (4 <= n_pre)) (PreH5 : (n_pre <= 100)) (PreH6 : (8 <= total)) (PreH7 : (total <= 200)) (PreH8 : ((Zlength (beads_l)) = n_pre)) (PreH9 : ((Zlength (dp_l)) = i)) (PreH10 : (0 <= i)) (PreH11 : (i <= (total * width ))) (PreH12 : (Forall (eq (0)) dp_l )) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : ((Zlength (beads_l)) = n_pre)) (PreH15 : (Forall (Z.le (1)) beads_l )) (PreH16 : (Forall (Z.ge (1000)) beads_l )) (PreH17 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 i dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) i (total * width ) )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (Forall (eq (0)) dp_l ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (i + 1 ) (total * width ) )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 i dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_6 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left split best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (((left * width ) + split ) * sizeof(INT)))) # Int  |-> (Znth ((left * width ) + split ) dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) ((left * width ) + split ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_7 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left split best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + ((((split + 1 ) * width ) + right ) * sizeof(INT)))) # Int  |-> (Znth (((split + 1 ) * width ) + right ) dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) (((split + 1 ) * width ) + right ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_8 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left split best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + (left * sizeof(INT)))) # Int  |-> (Znth left vals_l 0))
  **  (IntArray.missing_i ( &( "vals" ) ) left 0 total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_9 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left split best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + ((split + 1 ) * sizeof(INT)))) # Int  |-> (Znth (split + 1 ) vals_l 0))
  **  (IntArray.missing_i ( &( "vals" ) ) (split + 1 ) 0 total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_10 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (split: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : (left <= split)) (PreH13 : (split < right)) (PreH14 : (0 <= right)) (PreH15 : (right < total)) (PreH16 : ((right + 1 ) < total)) (PreH17 : (0 <= ((left * width ) + split ))) (PreH18 : (((left * width ) + split ) < (total * width ))) (PreH19 : (0 <= (((split + 1 ) * width ) + right ))) (PreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) (PreH21 : (0 <= left)) (PreH22 : (left < total)) (PreH23 : (0 <= (split + 1 ))) (PreH24 : ((split + 1 ) < total)) (PreH25 : (0 <= (right + 1 ))) (PreH26 : ((right + 1 ) < total)) (PreH27 : ((Zlength (beads_l)) = n_pre)) (PreH28 : ((Zlength (dp_l)) = (total * width ))) (PreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH30 : (0 <= total)) (PreH31 : (width = total)) (PreH32 : ((Zlength (vals_l)) = total)) (PreH33 : ((Zlength (dp_l)) = (total * width ))) (PreH34 : (1 <= len)) (PreH35 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH36 : (2 <= len)) (PreH37 : (0 <= left)) (PreH38 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH39 : ((left + len ) <= total)) (PreH40 : (left <= split)) (PreH41 : (split <= ((left + len ) - 1 ))) (PreH42 : (0 <= best)) (PreH43 : (best <= 2100000000)) (PreH44 : (EnergySplitBest vals_l dp_l width len left split best )) (PreH45 : ((Zlength (beads_l)) = n_pre)) (PreH46 : (Forall (Z.le (1)) beads_l )) (PreH47 : (Forall (Z.ge (1000)) beads_l )) (PreH48 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= split) ” 
  &&  “ (split <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left split best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "vals" ) ) + ((right + 1 ) * sizeof(INT)))) # Int  |-> (Znth (right + 1 ) vals_l 0))
  **  (IntArray.missing_i ( &( "vals" ) ) (right + 1 ) 0 total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_11 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (len: Z) (left: Z) (right: Z) (best: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (2 <= len)) (PreH8 : (len <= n_pre)) (PreH9 : (0 <= left)) (PreH10 : (left < (total - len ))) (PreH11 : (right = ((left + len ) - 1 ))) (PreH12 : ((right + 1 ) < total)) (PreH13 : (0 <= ((left * width ) + right ))) (PreH14 : (((left * width ) + right ) < (total * width ))) (PreH15 : (0 <= best)) (PreH16 : (best <= 2100000000)) (PreH17 : ((Zlength (beads_l)) = n_pre)) (PreH18 : ((Zlength (dp_l)) = (total * width ))) (PreH19 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH20 : (0 <= total)) (PreH21 : (width = total)) (PreH22 : ((Zlength (vals_l)) = total)) (PreH23 : ((Zlength (dp_l)) = (total * width ))) (PreH24 : (1 <= len)) (PreH25 : (EnergyLengthsComplete vals_l dp_l width len )) (PreH26 : (2 <= len)) (PreH27 : (0 <= left)) (PreH28 : (EnergyLeftComplete vals_l dp_l width len left )) (PreH29 : ((left + len ) <= total)) (PreH30 : (left <= right)) (PreH31 : (right <= ((left + len ) - 1 ))) (PreH32 : (0 <= best)) (PreH33 : (best <= 2100000000)) (PreH34 : (EnergySplitBest vals_l dp_l width len left right best )) (PreH35 : (EnergyIntervalBest vals_l left right best )) (PreH36 : ((Zlength (beads_l)) = n_pre)) (PreH37 : (Forall (Z.le (1)) beads_l )) (PreH38 : (Forall (Z.ge (1000)) beads_l )) (PreH39 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
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
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= len) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width len ) ” 
  &&  “ (2 <= len) ” 
  &&  “ (0 <= left) ” 
  &&  “ (EnergyLeftComplete vals_l dp_l width len left ) ” 
  &&  “ ((left + len ) <= total) ” 
  &&  “ (left <= right) ” 
  &&  “ (right <= ((left + len ) - 1 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= 2100000000) ” 
  &&  “ (EnergySplitBest vals_l dp_l width len left right best ) ” 
  &&  “ (EnergyIntervalBest vals_l left right best ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (((left * width ) + right ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "dp" ) ) ((left * width ) + right ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Definition energyNecklace_partial_solve_wit_12 := 
forall (n_pre: Z) (beads_pre: Z) (beads_l: (@list Z)) (vals_l: (@list Z)) (dp_l: (@list Z)) (total: Z) (width: Z) (start_2: Z) (answer: Z) (PreH1 : (total = (2 * n_pre ))) (PreH2 : (width = total)) (PreH3 : (4 <= n_pre)) (PreH4 : (n_pre <= 100)) (PreH5 : (8 <= total)) (PreH6 : (total <= 200)) (PreH7 : (0 <= start_2)) (PreH8 : (start_2 < n_pre)) (PreH9 : (0 <= ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ))) (PreH10 : (((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) < (total * width ))) (PreH11 : ((Zlength (beads_l)) = n_pre)) (PreH12 : ((Zlength (dp_l)) = (total * width ))) (PreH13 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH14 : (0 <= total)) (PreH15 : (width = total)) (PreH16 : ((Zlength (vals_l)) = total)) (PreH17 : ((Zlength (dp_l)) = (total * width ))) (PreH18 : (1 <= (n_pre + 1 ))) (PreH19 : (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) )) (PreH20 : (EnergyValsDuplicated beads_l vals_l n_pre )) (PreH21 : ((Zlength (dp_l)) = (total * width ))) (PreH22 : (width = total)) (PreH23 : (0 <= start_2)) (PreH24 : (start_2 <= n_pre)) (PreH25 : (0 <= answer)) (PreH26 : (answer <= 2100000000)) (PreH27 : (EnergyAnswerBest vals_l n_pre start_2 answer )) (PreH28 : (EnergyIntervalBest vals_l start_2 ((start_2 + n_pre ) - 1 ) (Znth ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) dp_l 0) )) (PreH29 : ((Zlength (beads_l)) = n_pre)) (PreH30 : (Forall (Z.le (1)) beads_l )) (PreH31 : (Forall (Z.ge (1000)) beads_l )) (PreH32 : forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000))) ,
  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.full ( &( "dp" ) ) (total * width ) dp_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
|--
  “ (total = (2 * n_pre )) ” 
  &&  “ (width = total) ” 
  &&  “ (4 <= n_pre) ” 
  &&  “ (n_pre <= 100) ” 
  &&  “ (8 <= total) ” 
  &&  “ (total <= 200) ” 
  &&  “ (0 <= start_2) ” 
  &&  “ (start_2 < n_pre) ” 
  &&  “ (0 <= ((((start_2 * width ) + start_2 ) + n_pre ) - 1 )) ” 
  &&  “ (((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) < (total * width )) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ (0 <= total) ” 
  &&  “ (width = total) ” 
  &&  “ ((Zlength (vals_l)) = total) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (EnergyLengthsComplete vals_l dp_l width (n_pre + 1 ) ) ” 
  &&  “ (EnergyValsDuplicated beads_l vals_l n_pre ) ” 
  &&  “ ((Zlength (dp_l)) = (total * width )) ” 
  &&  “ (width = total) ” 
  &&  “ (0 <= start_2) ” 
  &&  “ (start_2 <= n_pre) ” 
  &&  “ (0 <= answer) ” 
  &&  “ (answer <= 2100000000) ” 
  &&  “ (EnergyAnswerBest vals_l n_pre start_2 answer ) ” 
  &&  “ (EnergyIntervalBest vals_l start_2 ((start_2 + n_pre ) - 1 ) (Znth ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) dp_l 0) ) ” 
  &&  “ ((Zlength (beads_l)) = n_pre) ” 
  &&  “ (Forall (Z.le (1)) beads_l ) ” 
  &&  “ (Forall (Z.ge (1000)) beads_l ) ” 
  &&  “ forall (ev: (@list Z)) , forall (start: Z) , forall (energy: Z) , (((((EnergyValsDuplicated beads_l ev n_pre ) /\ (0 <= start)) /\ (start < n_pre)) /\ (EnergyIntervalPlan ev start ((start + n_pre ) - 1 ) energy )) -> (energy <= 2100000000)) ”
  &&  (((( &( "dp" ) ) + (((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) ((((start_2 * width ) + start_2 ) + n_pre ) - 1 ) 0 (total * width ) dp_l )
  **  (IntArray.full beads_pre n_pre beads_l )
  **  (IntArray.full ( &( "vals" ) ) total vals_l )
  **  (IntArray.undef_seg ( &( "vals" ) ) (2 * n_pre ) 200 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((2 * n_pre ) * (2 * n_pre ) ) 40000 )
.

Module Type VC_Correct.


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
Axiom proof_of_energyNecklace_entail_wit_12_1 : energyNecklace_entail_wit_12_1.
Axiom proof_of_energyNecklace_entail_wit_12_2 : energyNecklace_entail_wit_12_2.
Axiom proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13.
Axiom proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14.
Axiom proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15.
Axiom proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16.
Axiom proof_of_energyNecklace_entail_wit_17 : energyNecklace_entail_wit_17.
Axiom proof_of_energyNecklace_entail_wit_18 : energyNecklace_entail_wit_18.
Axiom proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19.
Axiom proof_of_energyNecklace_entail_wit_20_1 : energyNecklace_entail_wit_20_1.
Axiom proof_of_energyNecklace_entail_wit_20_2 : energyNecklace_entail_wit_20_2.
Axiom proof_of_energyNecklace_entail_wit_21 : energyNecklace_entail_wit_21.
Axiom proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22.
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
