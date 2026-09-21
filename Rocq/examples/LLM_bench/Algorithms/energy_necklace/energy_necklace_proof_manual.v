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
From SimpleC.EE.LLM_bench.Algorithms.energy_necklace Require Import energy_necklace_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg IntArray.mixed_full IntArray.mixed_seg.

Lemma scratch_full_tail_undef : forall x k cap l,
  0 <= k <= cap ->
  IntArray.full x k l ** IntArray.undef_seg x k cap |-- IntArray.undef_full x cap.
Proof.
  intros x k cap l Hk.
  sep_apply (IntArray.full_to_undef_full x k l).
  sep_apply (IntArray.undef_full_to_undef_seg x k).
  sep_apply (IntArray.undef_seg_merge_to_undef_full x 0 k cap Hk).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (cap - 0) with cap by lia. entailer!.
Qed.
Lemma scratch_undef_full_split : forall x k cap,
  0 <= k <= cap ->
  IntArray.undef_full x cap |-- IntArray.undef_full x k ** IntArray.undef_seg x k cap.
Proof.
  intros x k cap Hk.
  sep_apply (IntArray.undef_full_split_to_undef_seg x k cap Hk).
  sep_apply (IntArray.undef_seg_to_undef_full x 0 k).
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (k - 0) with k by lia. entailer!.
Qed.
Require Import AUXLib.MonotonicList.

(* Proofs reused by the current witnesses, kept with their mathematical
   statements in this manual so they compile without a separate library. *)
Module ReusedProof.




Definition energyNecklace_entail_wit_2 :=
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
  **  (IntArray.undef_full dp_pre (total * width ) ).

Definition energyNecklace_entail_wit_3 :=
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
  **  (IntArray.undef_full dp_pre (total * width ) ).

Definition energyNecklace_entail_wit_4 :=
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
  **  (IntArray.undef_full dp_pre (total * width ) ).

Definition energyNecklace_entail_wit_5 :=
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
  **  (IntArray.undef_full dp_pre (total * width ) ).

Definition energyNecklace_entail_wit_6 :=
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
  **  (IntArray.undef_full dp_pre (total * width ) ).

Definition energyNecklace_entail_wit_7 :=
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
  **  (IntArray.undef_full dp_pre (total * width ) ).

Definition energyNecklace_entail_wit_8 :=
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
  **  (IntArray.undef_seg dp_pre 0 (total * width ) ).

Definition energyNecklace_entail_wit_9 :=
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
  **  (IntArray.undef_seg dp_pre (i + 1 ) (total * width ) ).

Definition energyNecklace_entail_wit_10 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_12 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_13 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_14 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_15 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_16 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l_2 ).

Definition energyNecklace_entail_wit_17_2 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_17_1 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_19 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_20 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_new ).

Definition energyNecklace_entail_wit_22 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_24 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_25 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).



Definition energyNecklace_entail_wit_26 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_27 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l_2 ).

Definition energyNecklace_entail_wit_28_2 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_28_1 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).

Definition energyNecklace_entail_wit_30 :=
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
  **  (IntArray.full dp_pre (total * width ) dp_l ).


Lemma proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists (@nil Z).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg vals_pre total).
  rewrite (IntArray.seg_empty vals_pre 0 0).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.undef_seg vals_pre 0 total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
Qed.

Lemma proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists (vals_l_2 ++ Znth i beads_l 0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 (i + 1) (vals_l_2 ++ Znth i beads_l 0 :: nil)).
    cancel (IntArray.undef_seg vals_pre (i + 1) total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9; lia.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
      * rewrite app_Znth1 by lia.
        apply PreH12; lia.
      * assert (k = i) by lia.
        subst k.
        rewrite app_Znth2 by lia.
        rewrite PreH9.
        replace (i - i) with 0 by lia.
        simpl; reflexivity.
Qed.

Lemma proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists vals_l_2.
  split_pure_spatial.
  - rewrite Hi.
    cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 n_pre vals_l_2).
    cancel (IntArray.undef_seg vals_pre n_pre total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    intros k Hk.
    apply PreH12; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2.
  replace (n_pre + 0) with n_pre by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 n_pre vals_l_2).
    cancel (IntArray.undef_seg vals_pre n_pre total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
Qed.

Lemma proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists (vals_l_2 ++ Znth i beads_l 0 :: nil).
  replace (n_pre + (i + 1)) with ((n_pre + i) + 1) by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.seg vals_pre 0 ((n_pre + i) + 1)
              (vals_l_2 ++ Znth i beads_l 0 :: nil)).
    cancel (IntArray.undef_seg vals_pre ((n_pre + i) + 1) total).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9; lia.
    + intros k Hk.
      rewrite app_Znth1.
      * apply PreH12; lia.
      * rewrite PreH9; lia.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
      * rewrite app_Znth1.
        -- apply PreH13; lia.
        -- rewrite PreH9; lia.
      * assert (k = i) by lia.
        subst k.
        rewrite app_Znth2.
        -- rewrite PreH9.
           replace (n_pre + i - (n_pre + i)) with 0 by lia.
           simpl; reflexivity.
        -- rewrite PreH9; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  Exists vals_l_2.
  replace (n_pre + n_pre) with total by lia.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full vals_pre 0 total vals_l_2).
  replace (vals_pre + 0 * sizeof ( INT )) with vals_pre by nia.
  replace (total - 0) with total by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.undef_full dp_pre (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    unfold EnergyValsDuplicated.
    repeat split; try lia.
    + intros k Hk.
      apply PreH12; lia.
    + intros k Hk.
      apply PreH13; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 (@nil Z).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg dp_pre (total * width)).
  rewrite (IntArray.seg_empty dp_pre 0 0).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.undef_seg dp_pre 0 (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
Qed.

Lemma proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.seg dp_pre 0 (i + 1) (dp_l_2 ++ 0 :: nil)).
    cancel (IntArray.undef_seg dp_pre (i + 1) (total * width)).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH9; lia.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
      * rewrite app_Znth1 by lia.
        apply PreH12; lia.
      * assert (k = i) by lia.
        subst k.
        rewrite app_Znth2 by lia.
        rewrite PreH9.
        replace (i - i) with 0 by lia.
        simpl; reflexivity.
Qed.

Lemma proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hi : i = total * width) by lia.
  subst i.
  Exists vals_l_2 dp_l_2.
  rewrite Hi.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full dp_pre 0 (total * width) dp_l_2).
  replace (dp_pre + 0 * sizeof ( INT )) with dp_pre by nia.
  replace (total * width - 0) with (total * width) by lia.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.full dp_pre (total * width) dp_l_2).
  - split_pures; dump_pre_spatial; try solve [lia | eauto].
    + apply EnergyZeroTable_from_prefix__prefix_table_bootstrap with (i := total * width);
        try lia; auto.
      intros k Hk.
      apply PreH12; lia.
    + apply EnergyZeroTable_len_done_2__prefix_table_bootstrap.
      * unfold EnergyValsDuplicated in PreH13.
        destruct PreH13 as [_ [_ [Hvals _]]].
        lia.
      * apply EnergyZeroTable_from_prefix__prefix_table_bootstrap with (i := total * width);
          try lia; auto.
        intros k Hk.
        apply PreH12; lia.
Qed.

Lemma proof_of_energyNecklace_entail_wit_12 : energyNecklace_entail_wit_12.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    unfold EnergyLeftProgress, EnergyLenDone in *.
    repeat split; try tauto; try lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in *.
    repeat split; try tauto; try lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    all: unfold EnergySplitProgress in PreH19; lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    all: nia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hdone : EnergyLenDone vals_l dp_l total width len)
    by (unfold EnergySplitProgress, EnergyLeftProgress in PreH30; tauto).
  pose proof PreH32 as Hcomp_bound.
  destruct Hcomp_bound as [_ [Hsplit_bound [_ _]]].
  specialize (Hsplit_bound vals_l dp_l total width len left right split
                PreH29 PreH1 PreH2 ltac:(lia) ltac:(lia) PreH11
                ltac:(lia) PreH28 Hdone).
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hsplit_bound.
  destruct Hsplit_bound as [_ [_ [_ [_ Hcandidate_bound]]]].
  Exists vals_l dp_l.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l).
    cancel (IntArray.full dp_pre (total * width) dp_l).
  - split_pures; dump_pre_spatial; try reflexivity; try assumption; try lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_17_2 : energyNecklace_entail_wit_17_2.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hzvals : Zlength vals_l_2 = total)
    by (unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in PreH27; tauto).
  assert (Hcand : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate).
  {
    unfold EnergySplitCandidate, EnergyCellIndex.
    repeat split; try lia.
  }
  pose proof (EnergySplitProgress_step_keep__dp_interval_progress
                vals_l_2 dp_l_2 total width len left right split best candidate
                PreH12 ltac:(lia) PreH27 Hcand PreH22 PreH1) as Hstep.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    all: unfold EnergySplitProgress in PreH27; lia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_17_1 : energyNecklace_entail_wit_17_1.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hzvals : Zlength vals_l_2 = total)
    by (unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in PreH27; tauto).
  assert (Hcand : EnergySplitCandidate vals_l_2 dp_l_2 width left right split candidate).
  {
    unfold EnergySplitCandidate, EnergyCellIndex.
    repeat split; try lia.
  }
  pose proof (EnergySplitProgress_step_take__dp_interval_progress
                vals_l_2 dp_l_2 total width len left right split best candidate
                PreH12 ltac:(lia) PreH27 Hcand ltac:(lia) ltac:(lia)) as Hstep.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  all: dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hvals_len : Zlength vals_l_2 = total)
    by (unfold EnergySplitProgress, EnergyLeftProgress, EnergyLenDone in PreH24; tauto).
  assert (Hinterval : EnergyIntervalBest vals_l_2 left right best).
  {
    eapply EnergySplitProgress_finish_interval_best__dp_interval_progress.
    - exact PreH12.
    - exact PreH1.
    - rewrite Hvals_len; exact PreH16.
    - exact PreH24.
  }
  assert (Hsplit_right : EnergySplitProgress vals_l_2 dp_l_2 total width len left right best).
  {
    replace right with split by lia.
    exact PreH24.
  }
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    all: unfold EnergyCellIndex; nia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_20 : energyNecklace_entail_wit_20.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hupdated :
            EnergyUpdatedCell vals_l_2 dp_l
              (replace_Znth ((left * width) + right) best dp_l)
              width left right best).
  {
    unfold EnergyUpdatedCell.
    split.
    - rewrite PreH18.
      unfold EnergyCellIndex; lia.
    - split.
      + unfold EnergyCellIndex; reflexivity.
      + exact PreH21.
  }
  assert (Hleft_progress :
            EnergyLeftProgress vals_l_2
              (replace_Znth ((left * width) + right) best dp_l)
              total width len (left + 1)).
  {
    change (replace_Znth ((left * width) + right) best dp_l) with
      (replace_Znth (EnergyCellIndex width left right) best dp_l).
    apply EnergyLeftProgress_step_update__dp_interval_progress with (right := right);
      try assumption; try lia.
  }
  Exists vals_l_2 (replace_Znth ((left * width) + right) best dp_l) dp_l.
  split_pure_spatial.
  - cancel (IntArray.full beads_pre n_pre beads_l).
    cancel (IntArray.full vals_pre total vals_l_2).
    cancel (IntArray.full dp_pre (total * width)
              (replace_Znth ((left * width) + right) best dp_l)).
  - split_pures; dump_pre_spatial;
      try reflexivity; try assumption; try lia;
      try (rewrite Zlength_replace_Znth; lia).
Qed. 

Lemma proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22.
Proof.
  LLM_pre_process (lia || int_auto).
  assert (Hdone_next :
            EnergyLenDone vals_l_2 dp_l_2 total width (len + 1)).
  {
    apply EnergyLeftProgress_finish_len__dp_interval_progress with (left := left);
      try assumption; try lia.
  }
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_24 : energyNecklace_entail_wit_24.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    + unfold EnergyLenDone.
      repeat split; try assumption; try lia.
      unfold EnergyValsDuplicated in PreH12.
      destruct PreH12 as [_ [_ [Hvals _]]].
      lia.
      intros l left right idx Hl Hright Hidx Hleft Hbound.
      unfold EnergyLenDone in PreH13.
      destruct PreH13 as [_ [_ [_ [_ [_ Hdone]]]]].
      apply (Hdone l left right idx); try assumption; lia.
    + unfold EnergyAnswerProgress.
      repeat split; try assumption; try lia.
      all: try solve
        [ unfold EnergyValsDuplicated in PreH12;
          destruct PreH12 as [_ [_ [Hvals [Hcopy_low Hcopy_high]]]];
          try lia; eauto
        | left; split; lia ].
Qed. 

Lemma proof_of_energyNecklace_entail_wit_25 : energyNecklace_entail_wit_25.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_answer_bounds__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width 0 answer PreH11) as Hanswer_bounds.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed. 





Lemma proof_of_energyNecklace_entail_wit_26 : energyNecklace_entail_wit_26.
Proof.
  LLM_pre_process (lia || int_auto).
  pose proof (EnergyLenDone_rotation_cell_best__answer_loop
    vals_l_2 dp_l_2 total width n_pre start
    PreH4 PreH2 PreH3 ltac:(lia) PreH15) as Hbest.
  unfold EnergyCellIndex in Hbest.
  replace (start * width + (start + n_pre - 1))
    with ((((start * width) + start) + n_pre) - 1) in Hbest by lia.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; try lia; try nia.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_27 : energyNecklace_entail_wit_27.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l.
  pose proof (EnergyAnswerCellBounded__answer_loop
    beads_l vals_l_2 dp_l n_pre total width start
    PreH18 PreH13 PreH1 PreH2 ltac:(lia) PreH12 PreH14) as Hbounds.
  unfold EnergyCellIndex in Hbounds.
  replace (start * width + (start + n_pre - 1))
    with ((((start * width) + start) + n_pre) - 1) in Hbounds by lia.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_28_2 : energyNecklace_entail_wit_28_2.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_answer_bounds__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer PreH17) as Hanswer_bounds.
  pose proof (EnergyAnswerProgress_step_keep__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer value
    PreH17 ltac:(lia) PreH18 PreH11 PreH1) as Hprogress_next.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_28_1 : energyNecklace_entail_wit_28_1.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_step_update__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer value
    PreH17 ltac:(lia) PreH18 ltac:(lia) ltac:(lia)) as Hprogress_next.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed. 

Lemma proof_of_energyNecklace_entail_wit_30 : energyNecklace_entail_wit_30.
Proof.
  LLM_pre_process (lia || int_auto).
  Exists vals_l_2 dp_l_2.
  pose proof (EnergyAnswerProgress_finish__answer_loop
    beads_l vals_l_2 dp_l_2 n_pre total width start answer
    PreH4 PreH16 PreH1 PreH9) as Hanswer.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed. 

 

End ReusedProof.






Lemma energy_labels_reuse : forall beads n,
  Zlength beads = n -> Forall (Z.le 1) beads -> Forall (Z.ge 1000) beads ->
  EnergyLabelsBounded beads n.
Proof.
  intros beads n Hlen Hlo Hhi. split; [exact Hlen |].
  intros i Hi.
  pose proof (proj1 (Forall_Znth (Z.le 1) 0 beads) Hlo i ltac:(lia)) as H1.
  pose proof (proj1 (Forall_Znth (Z.ge 1000) 0 beads) Hhi i ltac:(lia)) as H2.
  apply Z.ge_le in H2. lia.
Qed.

Lemma energy_bounds_reuse beads n :
  1 <= n -> Zlength beads = n ->
  Forall (Z.le 1) beads -> Forall (Z.ge 1000) beads ->
  (forall vals start energy,
    ((EnergyValsDuplicated beads vals n /\ 0 <= start) /\ start < n) /\
    EnergyIntervalPlan vals start (start + n - 1) energy -> energy <= 2100000000) ->
  EnergyComputationBounded beads n 2100000000.
Proof.
  intros Hn Hlen Hlo Hhi Hb.
  apply EnergyComputationBounded_from_answer_bound; try lia.
  - apply energy_labels_reuse; assumption.
  - intros vals start energy Hd Hs Hp. apply (Hb vals start energy). tauto.
Qed.

Lemma energy_bounds_expand : forall (beads : list Z) (n : Z),
EnergyComputationBounded beads n 2100000000 ->
(forall (ev: (@list Z)) , forall (ed: (@list Z)) , forall (et: Z) , forall (ew: Z) , forall (el: Z) , forall (ea: Z) , forall (er: Z) , forall (es: Z) , ((((((((((((((((((EnergyValsDuplicated beads ev n ) /\ (et = (2 * n ))) /\ (ew = et)) /\ (2 <= el)) /\ (el <= n)) /\ (0 <= ea)) /\ (ea < (et - el ))) /\ (er = ((ea + el ) - 1 ))) /\ (ea <= es)) /\ (es < er)) /\ ((Zlength (ed)) = (et * ew ))) /\ (0 <= et)) /\ (ew = et)) /\ ((Zlength (ev)) = et)) /\ ((Zlength (ed)) = (et * ew ))) /\ (1 <= el)) /\ (EnergyLengthsComplete ev ed ew el )) -> ((((((((((0 <= (Znth ((ea * ew ) + es ) ed 0)) /\ ((Znth ((ea * ew ) + es ) ed 0) <= 2100000000)) /\ (0 <= (Znth (((es + 1 ) * ew ) + er ) ed 0))) /\ ((Znth (((es + 1 ) * ew ) + er ) ed 0) <= 2100000000)) /\ (0 <= (((Znth ea ev 0) * (Znth (es + 1 ) ev 0) ) * (Znth (er + 1 ) ev 0) ))) /\ ((((Znth ea ev 0) * (Znth (es + 1 ) ev 0) ) * (Znth (er + 1 ) ev 0) ) <= 2100000000)) /\ (0 <= ((Znth ((ea * ew ) + es ) ed 0) + (Znth (((es + 1 ) * ew ) + er ) ed 0) ))) /\ (((Znth ((ea * ew ) + es ) ed 0) + (Znth (((es + 1 ) * ew ) + er ) ed 0) ) <= 2100000000)) /\ (0 <= (((Znth ((ea * ew ) + es ) ed 0) + (Znth (((es + 1 ) * ew ) + er ) ed 0) ) + (((Znth ea ev 0) * (Znth (es + 1 ) ev 0) ) * (Znth (er + 1 ) ev 0) ) ))) /\ ((((Znth ((ea * ew ) + es ) ed 0) + (Znth (((es + 1 ) * ew ) + er ) ed 0) ) + (((Znth ea ev 0) * (Znth (es + 1 ) ev 0) ) * (Znth (er + 1 ) ev 0) ) ) <= 2100000000)))) /\
(forall (ev_2: (@list Z)) , forall (ea_2: Z) , forall (er_2: Z) , forall (ez: Z) , ((((((EnergyValsDuplicated beads ev_2 n ) /\ (0 <= ea_2)) /\ (ea_2 <= er_2)) /\ ((er_2 + 1 ) < (Zlength (ev_2)))) /\ (EnergyIntervalBest ev_2 ea_2 er_2 ez )) -> (er_2 - ea_2 + 1 <= n) -> ((0 <= ez) /\ (ez <= 2100000000)))) /\
(forall (ev_3: (@list Z)) , forall (ed_2: (@list Z)) , forall (et_2: Z) , forall (ew_2: Z) , forall (es_2: Z) , (((((((((((((EnergyValsDuplicated beads ev_3 n ) /\ (et_2 = (2 * n ))) /\ (ew_2 = et_2)) /\ (0 <= es_2)) /\ (es_2 < n)) /\ ((Zlength (ed_2)) = (et_2 * ew_2 ))) /\ (0 <= et_2)) /\ (ew_2 = et_2)) /\ ((Zlength (ev_3)) = et_2)) /\ ((Zlength (ed_2)) = (et_2 * ew_2 ))) /\ (1 <= (n + 1 ))) /\ (EnergyLengthsComplete ev_3 ed_2 ew_2 (n + 1 ) )) -> ((0 <= (Znth ((((es_2 * ew_2 ) + es_2 ) + n ) - 1 ) ed_2 0)) /\ ((Znth ((((es_2 * ew_2 ) + es_2 ) + n ) - 1 ) ed_2 0) <= 2100000000)))).
Proof.
  intros beads n (_ & H1 & H2 & H3). split.
  - intros vals dp total width len left right split Hargs.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    specialize (H1 vals dp total width len left right split
      ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(split; assumption)
      ltac:(split; assumption) ltac:(assumption) ltac:(split; assumption)
      ltac:(assumption) ltac:(unfold EnergyLenDone, EnergyLengthsComplete in *; repeat split; assumption)).
    unfold EnergySplitArithmeticBounded, EnergyCellIndex in H1. tauto.
  - split.
    + intros vals left right answer Hargs Hlen. apply (H2 vals left right answer); tauto.
    + intros vals dp total width start Hargs.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      specialize (H3 vals dp total width start
        ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(split; assumption)
        ltac:(assumption) ltac:(unfold EnergyLenDone, EnergyLengthsComplete in *; repeat split; assumption)).
      unfold EnergyCellIndex in H3.
      replace (start * width + start + n - 1) with (start * width + (start + n - 1)) by ring.
      exact H3.
Qed.

Lemma energy_labels_expand : forall beads n,
  EnergyLabelsBounded beads n ->
  Forall (Z.le 1) beads /\ Forall (Z.ge 1000) beads.
Proof.
  intros beads n [Hlen Hb]. split.
  - apply (proj2 (Forall_Znth (Z.le 1) 0 beads)). intros i Hi.
    specialize (Hb i ltac:(lia)). lia.
  - apply (proj2 (Forall_Znth (Z.ge 1000) 0 beads)). intros i Hi.
    specialize (Hb i ltac:(lia)). apply Z.le_ge. lia.
Qed.

Lemma energy_Forall2_eq : forall (xs ys : list Z), Forall2 eq xs ys <-> xs = ys.
Proof.
  intros xs ys. split.
  - intros H. induction H; subst; f_equal; assumption.
  - intros H. subst ys. induction xs; constructor; auto.
Qed.
Lemma energy_segments_agree : forall (xs ys : list Z) lo hi other_lo other_hi,
  0 <= lo <= hi /\ hi <= Zlength xs ->
  0 <= other_lo <= other_hi /\ other_hi <= Zlength ys ->
  hi - lo = other_hi - other_lo ->
  (Forall2 eq (sublist lo hi xs) (sublist other_lo other_hi ys) <->
   forall k, 0 <= k < hi - lo ->
     Znth (lo + k) xs 0 = Znth (other_lo + k) ys 0).
Proof.
  intros xs ys lo hi other_lo other_hi Hx Hy Hlength.
  rewrite energy_Forall2_eq, (list_eq_ext _ _ 0).
  rewrite !Zlength_sublist by lia. split.
  - intros [_ H] k Hk. specialize (H k Hk).
    rewrite !Znth_sublist in H by lia.
    replace (k + lo) with (lo + k) in H by lia.
    replace (k + other_lo) with (other_lo + k) in H by lia. exact H.
  - intros H. split; [lia |]. intros k Hk.
    rewrite !Znth_sublist by lia.
    replace (k + lo) with (lo + k) by lia.
    replace (k + other_lo) with (other_lo + k) by lia. apply H. exact Hk.
Qed.

Ltac energy_math :=
  try solve [assumption | reflexivity | eapply energy_labels_reuse; eassumption | eapply energy_bounds_reuse; (eassumption || lia)];
  repeat match goal with
  | H : Forall2 eq (sublist ?lo ?hi ?xs) (sublist ?olo ?ohi ?ys) |- _ =>
    let K := fresh "SegmentAgreement" in
    pose proof ((proj1 (energy_segments_agree xs ys lo hi olo ohi ltac:(lia) ltac:(lia) ltac:(lia))) H) as K; clear H
  | |- Forall2 eq (sublist ?lo ?hi ?xs) (sublist ?olo ?ohi ?ys) =>
    apply (proj2 (energy_segments_agree xs ys lo hi olo ohi ltac:(lia) ltac:(lia) ltac:(lia)))
  end;
  repeat match goal with
  | H : EnergyComputationBounded ?beads ?n 2100000000 |- _ =>
    let K := fresh "ExpandedBounds" in
    pose proof (energy_bounds_expand beads n H) as K; clear H; destruct K as [? [? ?]]
  | H : EnergyLabelsBounded ?beads ?n |- _ =>
    let K := fresh "ExpandedLabels" in
    pose proof (energy_labels_expand beads n H) as K; destruct K;
    unfold EnergyLabelsBounded in H; destruct H
  end;
  unfold EnergyComputationBounded, EnergySplitArithmeticBounded,
    EnergyLabelsBounded, EnergySplitProgress, EnergyLeftProgress,
    EnergyLenDone, EnergyZeroTable, EnergyUpdatedCell, EnergyAnswerProgress,
    EnergyLengthsComplete, EnergyLeftComplete, EnergySplitBest,
    EnergyAnswerBest, EnergyCellIndex in *;
  repeat match goal with
    | H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H
    | |- Forall ?P ?l => apply (proj2 (Forall_Znth P 0 l))
  end;
  unfold Z.ge in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | match goal with |- _ /\ _ => split end]; try lia;
  try solve [intros; repeat split; eauto 3; lia];
  try solve [intuition lia];
  try solve [intros; match goal with H : forall j : Z, _ -> _ |- _ => apply H; lia end];
  try solve [intros; match goal with |- context[Znth ?i ?xs 0] =>
    repeat match goal with H : forall j : Z, _ -> _ |- _ =>
      let K := fresh "AtIndex" in
      pose proof (H i ltac:(lia)) as K; clear H
    end; lia
  end].




































































Lemma proof_of_energyNecklace_safety_wit_25 : energyNecklace_safety_wit_25.
Proof.
  unfold energyNecklace_safety_wit_25; try left; intros.
  assert (LegacyPreH1 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH2 : (width = total)) by energy_math.
  assert (LegacyPreH3 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH4 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH5 : (8 <= total)) by energy_math.
  assert (LegacyPreH6 : (total <= 200)) by energy_math.
  assert (LegacyPreH7 : (2 <= len)) by energy_math.
  assert (LegacyPreH8 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH9 : (0 <= left)) by energy_math.
  assert (LegacyPreH10 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH11 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH12 : (left <= split)) by energy_math.
  assert (LegacyPreH13 : (split < right)) by energy_math.
  assert (LegacyPreH14 : (0 <= right)) by energy_math.
  assert (LegacyPreH15 : (right < total)) by energy_math.
  assert (LegacyPreH16 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH17 : (0 <= ((left * width ) + split ))) by energy_math.
  assert (LegacyPreH18 : (((left * width ) + split ) < (total * width ))) by energy_math.
  assert (LegacyPreH19 : (0 <= (((split + 1 ) * width ) + right ))) by energy_math.
  assert (LegacyPreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) by energy_math.
  assert (LegacyPreH21 : (0 <= left)) by energy_math.
  assert (LegacyPreH22 : (left < total)) by energy_math.
  assert (LegacyPreH23 : (0 <= (split + 1 ))) by energy_math.
  assert (LegacyPreH24 : ((split + 1 ) < total)) by energy_math.
  assert (LegacyPreH25 : (0 <= (right + 1 ))) by energy_math.
  assert (LegacyPreH26 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH27 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH28 : ((Zlength (dp_l)) = (total * width ))) by energy_math.
  assert (LegacyPreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) by energy_math.
  assert (LegacyPreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) by energy_math.
  assert (LegacyPreH31 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.


  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       LegacyPreH32 LegacyPreH29 LegacyPreH1 LegacyPreH2 (conj LegacyPreH7 LegacyPreH8) (conj LegacyPreH9 LegacyPreH10)
       LegacyPreH11 (conj LegacyPreH12 LegacyPreH13) LegacyPreH28 LegacyPreH30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [Hgain _]]].
  split_pures; dump_pre_spatial; lia.

Qed.

Lemma proof_of_energyNecklace_safety_wit_27 : energyNecklace_safety_wit_27.
Proof.
  unfold energyNecklace_safety_wit_27; try left; intros.
  assert (LegacyPreH1 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH2 : (width = total)) by energy_math.
  assert (LegacyPreH3 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH4 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH5 : (8 <= total)) by energy_math.
  assert (LegacyPreH6 : (total <= 200)) by energy_math.
  assert (LegacyPreH7 : (2 <= len)) by energy_math.
  assert (LegacyPreH8 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH9 : (0 <= left)) by energy_math.
  assert (LegacyPreH10 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH11 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH12 : (left <= split)) by energy_math.
  assert (LegacyPreH13 : (split < right)) by energy_math.
  assert (LegacyPreH14 : (0 <= right)) by energy_math.
  assert (LegacyPreH15 : (right < total)) by energy_math.
  assert (LegacyPreH16 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH17 : (0 <= ((left * width ) + split ))) by energy_math.
  assert (LegacyPreH18 : (((left * width ) + split ) < (total * width ))) by energy_math.
  assert (LegacyPreH19 : (0 <= (((split + 1 ) * width ) + right ))) by energy_math.
  assert (LegacyPreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) by energy_math.
  assert (LegacyPreH21 : (0 <= left)) by energy_math.
  assert (LegacyPreH22 : (left < total)) by energy_math.
  assert (LegacyPreH23 : (0 <= (split + 1 ))) by energy_math.
  assert (LegacyPreH24 : ((split + 1 ) < total)) by energy_math.
  assert (LegacyPreH25 : (0 <= (right + 1 ))) by energy_math.
  assert (LegacyPreH26 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH27 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH28 : ((Zlength (dp_l)) = (total * width ))) by energy_math.
  assert (LegacyPreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) by energy_math.
  assert (LegacyPreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) by energy_math.
  assert (LegacyPreH31 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.


  pose proof
    (EnergyValsDuplicated_label_bound__arithmetic_safety_bounds
       beads_l vals_l n_pre left LegacyPreH29 LegacyPreH31) as Hleft_bound.
  pose proof
    (EnergyValsDuplicated_label_bound__arithmetic_safety_bounds
       beads_l vals_l n_pre (split + 1) LegacyPreH29 LegacyPreH31) as Hsplit_bound.
  specialize (Hleft_bound ltac:(lia)).
  specialize (Hsplit_bound ltac:(lia)).
  split_pures; dump_pre_spatial; nia.

Qed.

Lemma proof_of_energyNecklace_safety_wit_31 : energyNecklace_safety_wit_31.
Proof.
  unfold energyNecklace_safety_wit_31; try left; intros.
  assert (LegacyPreH1 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH2 : (width = total)) by energy_math.
  assert (LegacyPreH3 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH4 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH5 : (8 <= total)) by energy_math.
  assert (LegacyPreH6 : (total <= 200)) by energy_math.
  assert (LegacyPreH7 : (2 <= len)) by energy_math.
  assert (LegacyPreH8 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH9 : (0 <= left)) by energy_math.
  assert (LegacyPreH10 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH11 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH12 : (left <= split)) by energy_math.
  assert (LegacyPreH13 : (split < right)) by energy_math.
  assert (LegacyPreH14 : (0 <= right)) by energy_math.
  assert (LegacyPreH15 : (right < total)) by energy_math.
  assert (LegacyPreH16 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH17 : (0 <= ((left * width ) + split ))) by energy_math.
  assert (LegacyPreH18 : (((left * width ) + split ) < (total * width ))) by energy_math.
  assert (LegacyPreH19 : (0 <= (((split + 1 ) * width ) + right ))) by energy_math.
  assert (LegacyPreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) by energy_math.
  assert (LegacyPreH21 : (0 <= left)) by energy_math.
  assert (LegacyPreH22 : (left < total)) by energy_math.
  assert (LegacyPreH23 : (0 <= (split + 1 ))) by energy_math.
  assert (LegacyPreH24 : ((split + 1 ) < total)) by energy_math.
  assert (LegacyPreH25 : (0 <= (right + 1 ))) by energy_math.
  assert (LegacyPreH26 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH27 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH28 : ((Zlength (dp_l)) = (total * width ))) by energy_math.
  assert (LegacyPreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) by energy_math.
  assert (LegacyPreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) by energy_math.
  assert (LegacyPreH31 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.


  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       LegacyPreH32 LegacyPreH29 LegacyPreH1 LegacyPreH2 (conj LegacyPreH7 LegacyPreH8) (conj LegacyPreH9 LegacyPreH10)
       LegacyPreH11 (conj LegacyPreH12 LegacyPreH13) LegacyPreH28 LegacyPreH30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [_ [_ Hcandidate]]]].
  split_pures; dump_pre_spatial; lia.

Qed.

Lemma proof_of_energyNecklace_safety_wit_32 : energyNecklace_safety_wit_32.
Proof.
  unfold energyNecklace_safety_wit_32; try left; intros.
  assert (LegacyPreH1 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH2 : (width = total)) by energy_math.
  assert (LegacyPreH3 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH4 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH5 : (8 <= total)) by energy_math.
  assert (LegacyPreH6 : (total <= 200)) by energy_math.
  assert (LegacyPreH7 : (2 <= len)) by energy_math.
  assert (LegacyPreH8 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH9 : (0 <= left)) by energy_math.
  assert (LegacyPreH10 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH11 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH12 : (left <= split)) by energy_math.
  assert (LegacyPreH13 : (split < right)) by energy_math.
  assert (LegacyPreH14 : (0 <= right)) by energy_math.
  assert (LegacyPreH15 : (right < total)) by energy_math.
  assert (LegacyPreH16 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH17 : (0 <= ((left * width ) + split ))) by energy_math.
  assert (LegacyPreH18 : (((left * width ) + split ) < (total * width ))) by energy_math.
  assert (LegacyPreH19 : (0 <= (((split + 1 ) * width ) + right ))) by energy_math.
  assert (LegacyPreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) by energy_math.
  assert (LegacyPreH21 : (0 <= left)) by energy_math.
  assert (LegacyPreH22 : (left < total)) by energy_math.
  assert (LegacyPreH23 : (0 <= (split + 1 ))) by energy_math.
  assert (LegacyPreH24 : ((split + 1 ) < total)) by energy_math.
  assert (LegacyPreH25 : (0 <= (right + 1 ))) by energy_math.
  assert (LegacyPreH26 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH27 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH28 : ((Zlength (dp_l)) = (total * width ))) by energy_math.
  assert (LegacyPreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) by energy_math.
  assert (LegacyPreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) by energy_math.
  assert (LegacyPreH31 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.


  pose proof
    (EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds
       beads_l vals_l dp_l n_pre total width len left right split best 2100000000
       LegacyPreH32 LegacyPreH29 LegacyPreH1 LegacyPreH2 (conj LegacyPreH7 LegacyPreH8) (conj LegacyPreH9 LegacyPreH10)
       LegacyPreH11 (conj LegacyPreH12 LegacyPreH13) LegacyPreH28 LegacyPreH30) as Hbounds.
  unfold EnergySplitArithmeticBounded, EnergyCellIndex in Hbounds.
  destruct Hbounds as [_ [_ [_ [Hsum _]]]].
  split_pures; dump_pre_spatial; lia.

Qed.

Lemma proof_of_energyNecklace_entail_wit_1 : energyNecklace_entail_wit_1.
Proof.
  unfold energyNecklace_entail_wit_1; left; intros.
  sep_apply (scratch_undef_full_split (&("vals")) (2*n_pre) 200 ltac:(nia)).
  sep_apply (scratch_undef_full_split (&("dp")) ((2*n_pre)*(2*n_pre)) 40000 ltac:(nia)).
  sep_apply (IntArray.undef_full_to_undef_seg (&("vals")) (2*n_pre)).
  Exists (@nil Z). rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_energyNecklace_entail_wit_2 : energyNecklace_entail_wit_2.
Proof.
  unfold energyNecklace_entail_wit_2; try left; intros.
  assert (LegacyPreH1 : (i < n_pre)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH9 : ((Zlength (vals_l_2)) = i)) by energy_math.
  assert (LegacyPreH10 : (0 <= i)) by energy_math.
  assert (LegacyPreH11 : (i <= n_pre)) by energy_math.
  assert (LegacyPreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) by energy_math.
  assert (LegacyPreH13 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_3 (&("dp")) (&("vals")) n_pre beads_pre beads_l i vals_l_2 width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused.
  Exists vals_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_3 : energyNecklace_entail_wit_3.
Proof.
  unfold energyNecklace_entail_wit_3; try left; intros.
  assert (LegacyPreH1 : (i >= n_pre)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH9 : ((Zlength (vals_l_2)) = i)) by energy_math.
  assert (LegacyPreH10 : (0 <= i)) by energy_math.
  assert (LegacyPreH11 : (i <= n_pre)) by energy_math.
  assert (LegacyPreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth k_2 vals_l_2 0) = (Znth k_2 beads_l 0)))) by energy_math.
  assert (LegacyPreH13 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH14 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_4 (&("dp")) (&("vals")) n_pre beads_pre beads_l i vals_l_2 width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused.
  Exists vals_l_reused.
  replace (n_pre+0) with n_pre by lia.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_4 : energyNecklace_entail_wit_4.
Proof.
  unfold energyNecklace_entail_wit_4; try left; intros.
  assert (LegacyPreH1 : (i < n_pre)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) by energy_math.
  assert (LegacyPreH10 : (0 <= i)) by energy_math.
  assert (LegacyPreH11 : (i <= n_pre)) by energy_math.
  assert (LegacyPreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) by energy_math.
  assert (LegacyPreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) by energy_math.
  assert (LegacyPreH14 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_6 (&("dp")) (&("vals")) n_pre beads_pre beads_l i vals_l_2 width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused.
  Exists vals_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_5 : energyNecklace_entail_wit_5.
Proof.
  unfold energyNecklace_entail_wit_5; try left; intros.
  assert (Hwork_nonnegative : 0 <= total * width) by (apply Z.mul_nonneg_nonneg; lia).
  assert (LegacyPreH1 : (i >= n_pre)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH9 : ((Zlength (vals_l_2)) = (n_pre + i ))) by energy_math.
  assert (LegacyPreH10 : (0 <= i)) by energy_math.
  assert (LegacyPreH11 : (i <= n_pre)) by energy_math.
  assert (LegacyPreH12 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth k vals_l_2 0) = (Znth k beads_l 0)))) by energy_math.
  assert (LegacyPreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (n_pre + k_2 ) vals_l_2 0) = (Znth k_2 beads_l 0)))) by energy_math.
  assert (LegacyPreH14 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_7 (&("dp")) (&("vals")) n_pre beads_pre beads_l i vals_l_2 width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused.
  Exists vals_l_reused (@nil Z).
  sep_apply (IntArray.undef_full_to_undef_seg (&("dp")) (total*width)).
  rewrite IntArray.seg_empty.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try solve [assumption | constructor | reflexivity]; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_6 : energyNecklace_entail_wit_6.
Proof.
  unfold energyNecklace_entail_wit_6; try left; intros.
  assert (LegacyPreH1 : (i < (total * width ))) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH9 : ((Zlength (dp_l_2)) = i)) by energy_math.
  assert (LegacyPreH10 : (0 <= i)) by energy_math.
  assert (LegacyPreH11 : (i <= (total * width ))) by energy_math.
  assert (LegacyPreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) by energy_math.
  assert (LegacyPreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH14 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_9 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 i dp_l_2 width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_7 : energyNecklace_entail_wit_7.
Proof.
  unfold energyNecklace_entail_wit_7; try left; intros.
  assert (LegacyPreH1 : (i >= (total * width ))) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH9 : ((Zlength (dp_l_2)) = i)) by energy_math.
  assert (LegacyPreH10 : (0 <= i)) by energy_math.
  assert (LegacyPreH11 : (i <= (total * width ))) by energy_math.
  assert (LegacyPreH12 : forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth k dp_l_2 0) = 0))) by energy_math.
  assert (LegacyPreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH14 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_10 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 i dp_l_2 width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_8 : energyNecklace_entail_wit_8.
Proof.
  unfold energyNecklace_entail_wit_8; try left; intros.
  assert (LegacyPreH1 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= (n_pre + 1 ))) by energy_math.
  assert (LegacyPreH10 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH11 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) by energy_math.
  assert (LegacyPreH14 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_12 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 len width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_9 : energyNecklace_entail_wit_9.
Proof.
  unfold energyNecklace_entail_wit_9; try left; intros.
  assert (LegacyPreH1 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH10 : (0 <= left)) by energy_math.
  assert (LegacyPreH11 : (left <= (total - len ))) by energy_math.
  assert (LegacyPreH12 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH13 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) by energy_math.
  assert (LegacyPreH16 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_13 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 left len width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_10 : energyNecklace_entail_wit_10.
Proof.
  unfold energyNecklace_entail_wit_10; try left; intros.
  assert (LegacyPreH1 : (split < right)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH10 : (0 <= left)) by energy_math.
  assert (LegacyPreH11 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH12 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH13 : (left < right)) by energy_math.
  assert (LegacyPreH14 : (0 <= right)) by energy_math.
  assert (LegacyPreH15 : (right < total)) by energy_math.
  assert (LegacyPreH16 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH17 : (left <= split)) by energy_math.
  assert (LegacyPreH18 : (split <= right)) by energy_math.
  assert (LegacyPreH19 : (0 <= best)) by energy_math.
  assert (LegacyPreH20 : (best <= 2100000000)) by energy_math.
  assert (LegacyPreH21 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH22 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) by energy_math.
  assert (LegacyPreH25 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_15 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 best split right left len width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_11 : energyNecklace_entail_wit_11.
Proof.
  unfold energyNecklace_entail_wit_11; try left; intros.
  assert (LegacyPreH1 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH2 : (width = total)) by energy_math.
  assert (LegacyPreH3 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH4 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH5 : (8 <= total)) by energy_math.
  assert (LegacyPreH6 : (total <= 200)) by energy_math.
  assert (LegacyPreH7 : (2 <= len)) by energy_math.
  assert (LegacyPreH8 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH9 : (0 <= left)) by energy_math.
  assert (LegacyPreH10 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH11 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH12 : (left <= split)) by energy_math.
  assert (LegacyPreH13 : (split < right)) by energy_math.
  assert (LegacyPreH14 : (0 <= right)) by energy_math.
  assert (LegacyPreH15 : (right < total)) by energy_math.
  assert (LegacyPreH16 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH17 : (0 <= ((left * width ) + split ))) by energy_math.
  assert (LegacyPreH18 : (((left * width ) + split ) < (total * width ))) by energy_math.
  assert (LegacyPreH19 : (0 <= (((split + 1 ) * width ) + right ))) by energy_math.
  assert (LegacyPreH20 : ((((split + 1 ) * width ) + right ) < (total * width ))) by energy_math.
  assert (LegacyPreH21 : (0 <= left)) by energy_math.
  assert (LegacyPreH22 : (left < total)) by energy_math.
  assert (LegacyPreH23 : (0 <= (split + 1 ))) by energy_math.
  assert (LegacyPreH24 : ((split + 1 ) < total)) by energy_math.
  assert (LegacyPreH25 : (0 <= (right + 1 ))) by energy_math.
  assert (LegacyPreH26 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH27 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH28 : ((Zlength (dp_l)) = (total * width ))) by energy_math.
  assert (LegacyPreH29 : (EnergyValsDuplicated beads_l vals_l n_pre )) by energy_math.
  assert (LegacyPreH30 : (EnergySplitProgress vals_l dp_l total width len left split best )) by energy_math.
  assert (LegacyPreH31 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH32 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_16 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l dp_l total width len left right split best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29 LegacyPreH30 LegacyPreH31 LegacyPreH32) as Hreused.
  sep_apply Hreused.
  Intros vals_l_2_reused dp_l_2_reused.
  Exists vals_l_2_reused dp_l_2_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_12_1 : energyNecklace_entail_wit_12_1.
Proof.
  unfold energyNecklace_entail_wit_12_1; try left; intros.
  assert (LegacyPreH1 : (candidate > best)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH10 : (0 <= left)) by energy_math.
  assert (LegacyPreH11 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH12 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH13 : (left <= split)) by energy_math.
  assert (LegacyPreH14 : (split < right)) by energy_math.
  assert (LegacyPreH15 : (0 <= right)) by energy_math.
  assert (LegacyPreH16 : (right < total)) by energy_math.
  assert (LegacyPreH17 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) by energy_math.
  assert (LegacyPreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) by energy_math.
  assert (LegacyPreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) by energy_math.
  assert (LegacyPreH21 : (candidate = ((left_value + right_value ) + gain ))) by energy_math.
  assert (LegacyPreH22 : (0 <= candidate)) by energy_math.
  assert (LegacyPreH23 : (candidate <= 2100000000)) by energy_math.
  assert (LegacyPreH24 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH25 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) by energy_math.
  assert (LegacyPreH28 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_17_1 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_12_2 : energyNecklace_entail_wit_12_2.
Proof.
  unfold energyNecklace_entail_wit_12_2; try left; intros.
  assert (LegacyPreH1 : (candidate <= best)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH10 : (0 <= left)) by energy_math.
  assert (LegacyPreH11 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH12 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH13 : (left <= split)) by energy_math.
  assert (LegacyPreH14 : (split < right)) by energy_math.
  assert (LegacyPreH15 : (0 <= right)) by energy_math.
  assert (LegacyPreH16 : (right < total)) by energy_math.
  assert (LegacyPreH17 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH18 : (left_value = (Znth ((left * width ) + split ) dp_l_2 0))) by energy_math.
  assert (LegacyPreH19 : (right_value = (Znth (((split + 1 ) * width ) + right ) dp_l_2 0))) by energy_math.
  assert (LegacyPreH20 : (gain = (((Znth left vals_l_2 0) * (Znth (split + 1 ) vals_l_2 0) ) * (Znth (right + 1 ) vals_l_2 0) ))) by energy_math.
  assert (LegacyPreH21 : (candidate = ((left_value + right_value ) + gain ))) by energy_math.
  assert (LegacyPreH22 : (0 <= candidate)) by energy_math.
  assert (LegacyPreH23 : (candidate <= 2100000000)) by energy_math.
  assert (LegacyPreH24 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH25 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH26 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH27 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) by energy_math.
  assert (LegacyPreH28 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH29 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_17_2 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 total width len left right split left_value right_value gain candidate best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26 LegacyPreH27 LegacyPreH28 LegacyPreH29) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_13 : energyNecklace_entail_wit_13.
Proof.
  unfold energyNecklace_entail_wit_13; left; intros.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_14 : energyNecklace_entail_wit_14.
Proof.
  unfold energyNecklace_entail_wit_14; try left; intros.
  assert (LegacyPreH1 : (split >= right)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH10 : (0 <= left)) by energy_math.
  assert (LegacyPreH11 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH12 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH13 : (left < right)) by energy_math.
  assert (LegacyPreH14 : (0 <= right)) by energy_math.
  assert (LegacyPreH15 : (right < total)) by energy_math.
  assert (LegacyPreH16 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH17 : (left <= split)) by energy_math.
  assert (LegacyPreH18 : (split <= right)) by energy_math.
  assert (LegacyPreH19 : (0 <= best)) by energy_math.
  assert (LegacyPreH20 : (best <= 2100000000)) by energy_math.
  assert (LegacyPreH21 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH22 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH23 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH24 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left split best )) by energy_math.
  assert (LegacyPreH25 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH26 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_19 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 best split right left len width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23 LegacyPreH24 LegacyPreH25 LegacyPreH26) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_15 : energyNecklace_entail_wit_15.
Proof.
  unfold energyNecklace_entail_wit_15; try left; intros.
  assert (LegacyPreH1 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH2 : (width = total)) by energy_math.
  assert (LegacyPreH3 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH4 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH5 : (8 <= total)) by energy_math.
  assert (LegacyPreH6 : (total <= 200)) by energy_math.
  assert (LegacyPreH7 : (2 <= len)) by energy_math.
  assert (LegacyPreH8 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH9 : (0 <= left)) by energy_math.
  assert (LegacyPreH10 : (left < (total - len ))) by energy_math.
  assert (LegacyPreH11 : (right = ((left + len ) - 1 ))) by energy_math.
  assert (LegacyPreH12 : ((right + 1 ) < total)) by energy_math.
  assert (LegacyPreH13 : (0 <= ((left * width ) + right ))) by energy_math.
  assert (LegacyPreH14 : (((left * width ) + right ) < (total * width ))) by energy_math.
  assert (LegacyPreH15 : (0 <= best)) by energy_math.
  assert (LegacyPreH16 : (best <= 2100000000)) by energy_math.
  assert (LegacyPreH17 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH18 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH19 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH20 : (EnergySplitProgress vals_l_2 dp_l_2 total width len left right best )) by energy_math.
  assert (LegacyPreH21 : (EnergyIntervalBest vals_l_2 left right best )) by energy_math.
  assert (LegacyPreH22 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH23 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_20 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 total width len left right best LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20 LegacyPreH21 LegacyPreH22 LegacyPreH23) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_new_reused dp_old_reused.
  Exists vals_l_reused dp_new_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_16 : energyNecklace_entail_wit_16.
Proof.
  unfold energyNecklace_entail_wit_16; try left; intros.
  assert (LegacyPreH1 : (left >= (total - len ))) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= n_pre)) by energy_math.
  assert (LegacyPreH10 : (0 <= left)) by energy_math.
  assert (LegacyPreH11 : (left <= (total - len ))) by energy_math.
  assert (LegacyPreH12 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH13 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyLeftProgress vals_l_2 dp_l_2 total width len left )) by energy_math.
  assert (LegacyPreH16 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH17 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_22 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 left len width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_17 : energyNecklace_entail_wit_17.
Proof.
  unfold energyNecklace_entail_wit_17; try left; intros.
  assert (LegacyPreH1 : (len > n_pre)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (2 <= len)) by energy_math.
  assert (LegacyPreH9 : (len <= (n_pre + 1 ))) by energy_math.
  assert (LegacyPreH10 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH11 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH12 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH13 : (EnergyLenDone vals_l_2 dp_l_2 total width len )) by energy_math.
  assert (LegacyPreH14 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_24 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 len width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_18 : energyNecklace_entail_wit_18.
Proof.
  unfold energyNecklace_entail_wit_18; try left; intros.
  assert (LegacyPreH1 : (start < n_pre)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (0 <= start)) by energy_math.
  assert (LegacyPreH9 : (start <= n_pre)) by energy_math.
  assert (LegacyPreH10 : (0 <= answer)) by energy_math.
  assert (LegacyPreH11 : (answer <= 2100000000)) by energy_math.
  assert (LegacyPreH12 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH13 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH14 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH15 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) by energy_math.
  assert (LegacyPreH16 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) by energy_math.
  assert (LegacyPreH17 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_26 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 answer start width total LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_19 : energyNecklace_entail_wit_19.
Proof.
  unfold energyNecklace_entail_wit_19; try left; intros.
  assert (LegacyPreH1 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH2 : (width = total)) by energy_math.
  assert (LegacyPreH3 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH4 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH5 : (8 <= total)) by energy_math.
  assert (LegacyPreH6 : (total <= 200)) by energy_math.
  assert (LegacyPreH7 : (0 <= start)) by energy_math.
  assert (LegacyPreH8 : (start < n_pre)) by energy_math.
  assert (LegacyPreH9 : (0 <= ((((start * width ) + start ) + n_pre ) - 1 ))) by energy_math.
  assert (LegacyPreH10 : (((((start * width ) + start ) + n_pre ) - 1 ) < (total * width ))) by energy_math.
  assert (LegacyPreH11 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH12 : ((Zlength (dp_l)) = (total * width ))) by energy_math.
  assert (LegacyPreH13 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH14 : (EnergyLenDone vals_l_2 dp_l total width (n_pre + 1 ) )) by energy_math.
  assert (LegacyPreH15 : (EnergyAnswerProgress beads_l vals_l_2 dp_l n_pre total width start answer )) by energy_math.
  assert (LegacyPreH16 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l 0) )) by energy_math.
  assert (LegacyPreH17 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH18 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_27 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l total width start answer LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_2_reused.
  Exists vals_l_reused dp_l_2_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_20_1 : energyNecklace_entail_wit_20_1.
Proof.
  unfold energyNecklace_entail_wit_20_1; try left; intros.
  assert (LegacyPreH1 : (value > answer)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (0 <= start)) by energy_math.
  assert (LegacyPreH9 : (start < n_pre)) by energy_math.
  assert (LegacyPreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) by energy_math.
  assert (LegacyPreH11 : (0 <= value)) by energy_math.
  assert (LegacyPreH12 : (value <= 2100000000)) by energy_math.
  assert (LegacyPreH13 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH14 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) by energy_math.
  assert (LegacyPreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) by energy_math.
  assert (LegacyPreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) by energy_math.
  assert (LegacyPreH19 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_28_1 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 total width start value answer LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_20_2 : energyNecklace_entail_wit_20_2.
Proof.
  unfold energyNecklace_entail_wit_20_2; try left; intros.
  assert (LegacyPreH1 : (value <= answer)) by energy_math.
  assert (LegacyPreH2 : (total = (2 * n_pre ))) by energy_math.
  assert (LegacyPreH3 : (width = total)) by energy_math.
  assert (LegacyPreH4 : (4 <= n_pre)) by energy_math.
  assert (LegacyPreH5 : (n_pre <= 100)) by energy_math.
  assert (LegacyPreH6 : (8 <= total)) by energy_math.
  assert (LegacyPreH7 : (total <= 200)) by energy_math.
  assert (LegacyPreH8 : (0 <= start)) by energy_math.
  assert (LegacyPreH9 : (start < n_pre)) by energy_math.
  assert (LegacyPreH10 : (value = (Znth ((((start * width ) + start ) + n_pre ) - 1 ) dp_l_2 0))) by energy_math.
  assert (LegacyPreH11 : (0 <= value)) by energy_math.
  assert (LegacyPreH12 : (value <= 2100000000)) by energy_math.
  assert (LegacyPreH13 : ((Zlength (beads_l)) = n_pre)) by energy_math.
  assert (LegacyPreH14 : ((Zlength (dp_l_2)) = (total * width ))) by energy_math.
  assert (LegacyPreH15 : (EnergyValsDuplicated beads_l vals_l_2 n_pre )) by energy_math.
  assert (LegacyPreH16 : (EnergyLenDone vals_l_2 dp_l_2 total width (n_pre + 1 ) )) by energy_math.
  assert (LegacyPreH17 : (EnergyAnswerProgress beads_l vals_l_2 dp_l_2 n_pre total width start answer )) by energy_math.
  assert (LegacyPreH18 : (EnergyIntervalBest vals_l_2 start ((start + n_pre ) - 1 ) value )) by energy_math.
  assert (LegacyPreH19 : (EnergyLabelsBounded beads_l n_pre )) by energy_math.
  assert (LegacyPreH20 : (EnergyComputationBounded beads_l n_pre 2100000000 )) by energy_math.
  pose proof (ReusedProof.proof_of_energyNecklace_entail_wit_28_2 (&("dp")) (&("vals")) n_pre beads_pre beads_l vals_l_2 dp_l_2 total width start value answer LegacyPreH1 LegacyPreH2 LegacyPreH3 LegacyPreH4 LegacyPreH5 LegacyPreH6 LegacyPreH7 LegacyPreH8 LegacyPreH9 LegacyPreH10 LegacyPreH11 LegacyPreH12 LegacyPreH13 LegacyPreH14 LegacyPreH15 LegacyPreH16 LegacyPreH17 LegacyPreH18 LegacyPreH19 LegacyPreH20) as Hreused.
  sep_apply Hreused.
  Intros vals_l_reused dp_l_reused.
  Exists vals_l_reused dp_l_reused.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_21 : energyNecklace_entail_wit_21.
Proof.
  unfold energyNecklace_entail_wit_21; left; intros.
  Exists vals_l_2 dp_l_2.
  split_pure_spatial.
  - repeat cancel; try reflexivity.
  - split_pures; dump_pre_spatial; energy_math.
Qed.

Lemma proof_of_energyNecklace_entail_wit_22 : energyNecklace_entail_wit_22.
Proof.
  unfold energyNecklace_entail_wit_22; right; intros.
  assert (Hprogress : EnergyAnswerProgress beads_l vals_l dp_l n_pre total width start_2 answer) by energy_math.
  pose proof (EnergyAnswerProgress_finish__answer_loop beads_l vals_l dp_l n_pre total width start_2 answer ltac:(lia) Hprogress ltac:(lia) ltac:(lia)) as Hanswer.
  subst width total.
  sep_apply (scratch_full_tail_undef (&("vals")) (2*n_pre) 200 vals_l ltac:(nia)).
  sep_apply (scratch_full_tail_undef (&("dp")) ((2*n_pre)*(2*n_pre)) 40000 dp_l ltac:(nia)).
  entailer!.
Qed.
