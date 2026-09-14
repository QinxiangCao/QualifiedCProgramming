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
Require Import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_lib.
Local Open Scope sac.

(*----- Function swap_intervals -----*)

Definition swap_intervals_return_wit_1 := 
(
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full ed_pre n (replace_Znth (j_pre) ((Znth i_pre ed_l 0)) ((replace_Znth (i_pre) ((Znth j_pre ed_l 0)) (ed_l)))) )
  **  (IntArray.full st_pre n (replace_Znth (j_pre) ((Znth i_pre st_l 0)) ((replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)))) )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSwappedAt ps ps1 i_pre j_pre ) ”
  &&  (IntArray.full st_pre n st1 )
  **  (IntArray.full ed_pre n ed1 )
) \/
(
forall (j_pre: Z) (i_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (PairIntervals (replace_Znth (j_pre) ((Znth i_pre st_l 0)) ((replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)))) (replace_Znth (j_pre) ((Znth i_pre ed_l 0)) ((replace_Znth (i_pre) ((Znth j_pre ed_l 0)) (ed_l)))) ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSwappedAt ps ps1 i_pre j_pre ) ”
  &&  emp
).

Definition swap_intervals_partial_solve_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full st_pre n st_l )
  **  (IntArray.full ed_pre n ed_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((st_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre st_l 0))
  **  (IntArray.missing_i st_pre i_pre 0 n st_l )
  **  (IntArray.full ed_pre n ed_l )
.

Definition swap_intervals_partial_solve_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full st_pre n st_l )
  **  (IntArray.full ed_pre n ed_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((ed_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre ed_l 0))
  **  (IntArray.missing_i ed_pre i_pre 0 n ed_l )
  **  (IntArray.full st_pre n st_l )
.

Definition swap_intervals_partial_solve_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full ed_pre n ed_l )
  **  (IntArray.full st_pre n st_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((st_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre st_l 0))
  **  (IntArray.missing_i st_pre j_pre 0 n st_l )
  **  (IntArray.full ed_pre n ed_l )
.

Definition swap_intervals_partial_solve_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full st_pre n st_l )
  **  (IntArray.full ed_pre n ed_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((st_pre + (i_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre i_pre 0 n st_l )
  **  (IntArray.full ed_pre n ed_l )
.

Definition swap_intervals_partial_solve_wit_5 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)) )
  **  (IntArray.full ed_pre n ed_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((ed_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre ed_l 0))
  **  (IntArray.missing_i ed_pre j_pre 0 n ed_l )
  **  (IntArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)) )
.

Definition swap_intervals_partial_solve_wit_6 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full ed_pre n ed_l )
  **  (IntArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((ed_pre + (i_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ed_pre i_pre 0 n ed_l )
  **  (IntArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)) )
.

Definition swap_intervals_partial_solve_wit_7 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full ed_pre n (replace_Znth (i_pre) ((Znth j_pre ed_l 0)) (ed_l)) )
  **  (IntArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((st_pre + (j_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre j_pre 0 n (replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)) )
  **  (IntArray.full ed_pre n (replace_Znth (i_pre) ((Znth j_pre ed_l 0)) (ed_l)) )
.

Definition swap_intervals_partial_solve_wit_8 := 
forall (j_pre: Z) (i_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps )) (PreH6 : (IntervalBounds ps )) ,
  (IntArray.full st_pre n (replace_Znth (j_pre) ((Znth i_pre st_l 0)) ((replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)))) )
  **  (IntArray.full ed_pre n (replace_Znth (i_pre) ((Znth j_pre ed_l 0)) (ed_l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((ed_pre + (j_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ed_pre j_pre 0 n (replace_Znth (i_pre) ((Znth j_pre ed_l 0)) (ed_l)) )
  **  (IntArray.full st_pre n (replace_Znth (j_pre) ((Znth i_pre st_l 0)) ((replace_Znth (i_pre) ((Znth j_pre st_l 0)) (st_l)))) )
.

(*----- Function partition_intervals -----*)

Definition partition_intervals_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps )) (PreH5 : (IntervalBounds ps )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
  **  ((( &( "pivot_end" ) )) # Int  |-> (Znth high_pre ed_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition partition_intervals_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps )) (PreH5 : (IntervalBounds ps )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
  **  ((( &( "pivot_end" ) )) # Int  |-> (Znth high_pre ed_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_intervals_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : ((Znth j ed1 0) <= pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : ((Zlength (st1)) = intervalsSize_pre)) (PreH10 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH11 : (pivot_end = (Znth high_pre ed1 0))) (PreH12 : (PairIntervals st1 ed1 ps1 )) (PreH13 : (IntervalBounds ps1 )) (PreH14 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_intervals_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation ps1 ps1_2 )) (PreH4 : (IntervalSwappedAt ps1 ps1_2 (i + 1 ) j )) (PreH5 : ((Znth j ed1 0) <= pivot_end)) (PreH6 : (j < high_pre)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < intervalsSize_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (st1)) = intervalsSize_pre)) (PreH14 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH15 : (pivot_end = (Znth high_pre ed1 0))) (PreH16 : (PairIntervals st1 ed1 ps1 )) (PreH17 : (IntervalBounds ps1 )) (PreH18 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full st_pre (Zlength (st1)) st1_2 )
  **  (IntArray.full ed_pre (Zlength (st1)) ed1_2 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_intervals_safety_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : ((Znth j ed1 0) > pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : ((Zlength (st1)) = intervalsSize_pre)) (PreH10 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH11 : (pivot_end = (Znth high_pre ed1 0))) (PreH12 : (PairIntervals st1 ed1 ps1 )) (PreH13 : (IntervalBounds ps1 )) (PreH14 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_intervals_safety_wit_6 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (j >= high_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1 ) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : ((Zlength (st1)) = intervalsSize_pre)) (PreH9 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1 0))) (PreH11 : (PairIntervals st1 ed1 ps1 )) (PreH12 : (IntervalBounds ps1 )) (PreH13 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_intervals_safety_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (j >= high_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1 ) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : ((Zlength (st1)) = intervalsSize_pre)) (PreH9 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1 0))) (PreH11 : (PairIntervals st1 ed1 ps1 )) (PreH12 : (IntervalBounds ps1 )) (PreH13 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_intervals_safety_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation ps1 ps1_2 )) (PreH4 : (IntervalSwappedAt ps1 ps1_2 (i + 1 ) high_pre )) (PreH5 : (j >= high_pre)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < intervalsSize_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (st1)) = intervalsSize_pre)) (PreH13 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH14 : (pivot_end = (Znth high_pre ed1 0))) (PreH15 : (PairIntervals st1 ed1 ps1 )) (PreH16 : (IntervalBounds ps1 )) (PreH17 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full st_pre (Zlength (st1)) st1_2 )
  **  (IntArray.full ed_pre (Zlength (st1)) ed1_2 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_intervals_safety_wit_9 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation ps1 ps1_2 )) (PreH4 : (IntervalSwappedAt ps1 ps1_2 (i + 1 ) high_pre )) (PreH5 : (j >= high_pre)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < intervalsSize_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (st1)) = intervalsSize_pre)) (PreH13 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH14 : (pivot_end = (Znth high_pre ed1 0))) (PreH15 : (PairIntervals st1 ed1 ps1 )) (PreH16 : (IntervalBounds ps1 )) (PreH17 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full st_pre (Zlength (st1)) st1_2 )
  **  (IntArray.full ed_pre (Zlength (st1)) ed1_2 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_intervals_entail_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps )) (PreH5 : (IntervalBounds ps )) ,
  ((( &( "j" ) )) # Int  |-> low_pre)
  **  ((( &( "i" ) )) # Int  |-> (low_pre - 1 ))
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
  **  ((( &( "pivot_end" ) )) # Int  |-> (Znth high_pre ed_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
|--
  EX (ps1: (@list interval))  (pivot_end: Z)  (ed1: (@list Z))  (st1: (@list Z))  (j: Z)  (i: Z) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < intervalsSize_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (st1)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (ed1)) = intervalsSize_pre) ” 
  &&  “ (pivot_end = (Znth high_pre ed1 0)) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end ) ”
  &&  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : ((Zlength (st_l)) = intervalsSize_pre)) (PreH2 : ((Zlength (ed_l)) = intervalsSize_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps )) (PreH7 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre (low_pre - 1 ) low_pre (Znth high_pre ed_l 0) ) ”
  &&  emp
).

Definition partition_intervals_entail_wit_2_1 := 
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end_2: Z) (j_2: Z) (i_2: Z) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (st1_3: (@list Z)) (ed1_3: (@list Z)) (ps1_3: (@list interval)) (PreH1 : (PairIntervals st1_3 ed1_3 ps1_3 )) (PreH2 : (IntervalBounds ps1_3 )) (PreH3 : (IntervalPermutation ps1_2 ps1_3 )) (PreH4 : (IntervalSwappedAt ps1_2 ps1_3 (i_2 + 1 ) j_2 )) (PreH5 : ((Znth j_2 ed1_2 0) <= pivot_end_2)) (PreH6 : (j_2 < high_pre)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < intervalsSize_pre)) (PreH10 : ((low_pre - 1 ) <= i_2)) (PreH11 : (i_2 < j_2)) (PreH12 : (j_2 <= high_pre)) (PreH13 : ((Zlength (st1_2)) = intervalsSize_pre)) (PreH14 : ((Zlength (ed1_2)) = intervalsSize_pre)) (PreH15 : (pivot_end_2 = (Znth high_pre ed1_2 0))) (PreH16 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH17 : (IntervalBounds ps1_2 )) (PreH18 : (LomutoScanState ps ps1_2 low_pre high_pre i_2 j_2 pivot_end_2 )) ,
  (IntArray.full st_pre (Zlength (st1_2)) st1_3 )
  **  (IntArray.full ed_pre (Zlength (st1_2)) ed1_3 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end_2)
|--
  EX (ps1: (@list interval))  (pivot_end: Z)  (ed1: (@list Z))  (st1: (@list Z))  (j: Z)  (i: Z) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < intervalsSize_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (st1)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (ed1)) = intervalsSize_pre) ” 
  &&  “ (pivot_end = (Znth high_pre ed1 0)) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end ) ”
  &&  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (pivot_end_2: Z) (j_2: Z) (i_2: Z) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (st1_3: (@list Z)) (ed1_3: (@list Z)) (ps1_3: (@list interval)) (PreH1 : ((Zlength (ed1_3)) = (Zlength (st1_2)))) (PreH2 : ((Zlength (st1_3)) = (Zlength (st1_2)))) (PreH3 : (PairIntervals st1_3 ed1_3 ps1_3 )) (PreH4 : (IntervalBounds ps1_3 )) (PreH5 : (IntervalPermutation ps1_2 ps1_3 )) (PreH6 : (IntervalSwappedAt ps1_2 ps1_3 (i_2 + 1 ) j_2 )) (PreH7 : ((Znth j_2 ed1_2 0) <= pivot_end_2)) (PreH8 : (j_2 < high_pre)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < intervalsSize_pre)) (PreH12 : ((low_pre - 1 ) <= i_2)) (PreH13 : (i_2 < j_2)) (PreH14 : (j_2 <= high_pre)) (PreH15 : ((Zlength (st1_2)) = intervalsSize_pre)) (PreH16 : ((Zlength (ed1_2)) = intervalsSize_pre)) (PreH17 : (pivot_end_2 = (Znth high_pre ed1_2 0))) (PreH18 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH19 : (IntervalBounds ps1_2 )) (PreH20 : (LomutoScanState ps ps1_2 low_pre high_pre i_2 j_2 pivot_end_2 )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ ((Znth high_pre ed1_2 0) = (Znth high_pre ed1_3 0)) ” 
  &&  “ ((Znth high_pre ed1_2 0) = (Znth high_pre ed1_3 0)) ” 
  &&  “ ((low_pre - 1 ) <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) < (j_2 + 1 )) ” 
  &&  “ ((j_2 + 1 ) <= high_pre) ” 
  &&  “ (PairIntervals st1_3 ed1_3 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre (i_2 + 1 ) (j_2 + 1 ) (Znth high_pre ed1_3 0) ) ”
  &&  emp
).

Definition partition_intervals_entail_wit_2_2 := 
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end_2: Z) (j_2: Z) (i_2: Z) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : ((Znth j_2 ed1_2 0) > pivot_end_2)) (PreH2 : (j_2 < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1 ) <= i_2)) (PreH7 : (i_2 < j_2)) (PreH8 : (j_2 <= high_pre)) (PreH9 : ((Zlength (st1_2)) = intervalsSize_pre)) (PreH10 : ((Zlength (ed1_2)) = intervalsSize_pre)) (PreH11 : (pivot_end_2 = (Znth high_pre ed1_2 0))) (PreH12 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH13 : (IntervalBounds ps1_2 )) (PreH14 : (LomutoScanState ps ps1_2 low_pre high_pre i_2 j_2 pivot_end_2 )) ,
  (IntArray.full ed_pre intervalsSize_pre ed1_2 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end_2)
  **  (IntArray.full st_pre intervalsSize_pre st1_2 )
|--
  EX (ps1: (@list interval))  (pivot_end: Z)  (ed1: (@list Z))  (st1: (@list Z))  (j: Z)  (i: Z) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < intervalsSize_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (st1)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (ed1)) = intervalsSize_pre) ” 
  &&  “ (pivot_end = (Znth high_pre ed1 0)) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end ) ”
  &&  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (pivot_end_2: Z) (j_2: Z) (i_2: Z) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : ((Znth j_2 ed1_2 0) > pivot_end_2)) (PreH2 : (j_2 < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1 ) <= i_2)) (PreH7 : (i_2 < j_2)) (PreH8 : (j_2 <= high_pre)) (PreH9 : ((Zlength (st1_2)) = intervalsSize_pre)) (PreH10 : ((Zlength (ed1_2)) = intervalsSize_pre)) (PreH11 : (pivot_end_2 = (Znth high_pre ed1_2 0))) (PreH12 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH13 : (IntervalBounds ps1_2 )) (PreH14 : (LomutoScanState ps ps1_2 low_pre high_pre i_2 j_2 pivot_end_2 )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (i_2 < (j_2 + 1 )) ” 
  &&  “ ((j_2 + 1 ) <= high_pre) ” 
  &&  “ (PairIntervals st1_2 ed1_2 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre i_2 (j_2 + 1 ) (Znth high_pre ed1_2 0) ) ”
  &&  emp
).

Definition partition_intervals_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (st1_3: (@list Z)) (ed1_3: (@list Z)) (ps1_3: (@list interval)) (PreH1 : (PairIntervals st1_3 ed1_3 ps1_3 )) (PreH2 : (IntervalBounds ps1_3 )) (PreH3 : (IntervalPermutation ps1_2 ps1_3 )) (PreH4 : (IntervalSwappedAt ps1_2 ps1_3 (i + 1 ) high_pre )) (PreH5 : (j >= high_pre)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < intervalsSize_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (st1_2)) = intervalsSize_pre)) (PreH13 : ((Zlength (ed1_2)) = intervalsSize_pre)) (PreH14 : (pivot_end = (Znth high_pre ed1_2 0))) (PreH15 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH16 : (IntervalBounds ps1_2 )) (PreH17 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end )) ,
  (IntArray.full st_pre (Zlength (st1_2)) st1_3 )
  **  (IntArray.full ed_pre (Zlength (st1_2)) ed1_3 )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 low_pre high_pre ) ” 
  &&  “ (IntervalPartitionedAt ps1 low_pre high_pre (i + 1 ) ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (st1_3: (@list Z)) (ed1_3: (@list Z)) (ps1_3: (@list interval)) (PreH1 : (PairIntervals st1_3 ed1_3 ps1_3 )) (PreH2 : (IntervalBounds ps1_3 )) (PreH3 : (IntervalPermutation ps1_2 ps1_3 )) (PreH4 : (IntervalSwappedAt ps1_2 ps1_3 (i + 1 ) high_pre )) (PreH5 : (j >= high_pre)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < intervalsSize_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (st1_2)) = intervalsSize_pre)) (PreH13 : ((Zlength (ed1_2)) = intervalsSize_pre)) (PreH14 : (pivot_end = (Znth high_pre ed1_2 0))) (PreH15 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH16 : (IntervalBounds ps1_2 )) (PreH17 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ (PairIntervals st1_3 ed1_3 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 low_pre high_pre ) ” 
  &&  “ (IntervalPartitionedAt ps1 low_pre high_pre (i + 1 ) ) ”
  &&  emp
).

Definition partition_intervals_partial_solve_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps )) (PreH5 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < intervalsSize_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((ed_pre + (high_pre * sizeof(INT)))) # Int  |-> (Znth high_pre ed_l 0))
  **  (IntArray.missing_i ed_pre high_pre 0 intervalsSize_pre ed_l )
  **  (IntArray.full st_pre intervalsSize_pre st_l )
.

Definition partition_intervals_partial_solve_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (j < high_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1 ) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : ((Zlength (st1)) = intervalsSize_pre)) (PreH9 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1 0))) (PreH11 : (PairIntervals st1 ed1 ps1 )) (PreH12 : (IntervalBounds ps1 )) (PreH13 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < intervalsSize_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (st1)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (ed1)) = intervalsSize_pre) ” 
  &&  “ (pivot_end = (Znth high_pre ed1 0)) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end ) ”
  &&  (((ed_pre + (j * sizeof(INT)))) # Int  |-> (Znth j ed1 0))
  **  (IntArray.missing_i ed_pre j 0 intervalsSize_pre ed1 )
  **  (IntArray.full st_pre intervalsSize_pre st1 )
.

Definition partition_intervals_partial_solve_wit_3_pure := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : ((Znth j ed1 0) <= pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : ((Zlength (st1)) = intervalsSize_pre)) (PreH10 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH11 : (pivot_end = (Znth high_pre ed1 0))) (PreH12 : (PairIntervals st1 ed1 ps1 )) (PreH13 : (IntervalBounds ps1 )) (PreH14 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength (st1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength (st1))) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ”
.

Definition partition_intervals_partial_solve_wit_3_aux := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : ((Znth j ed1 0) <= pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : ((Zlength (st1)) = intervalsSize_pre)) (PreH10 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH11 : (pivot_end = (Znth high_pre ed1 0))) (PreH12 : (PairIntervals st1 ed1 ps1 )) (PreH13 : (IntervalBounds ps1 )) (PreH14 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  (IntArray.full st_pre intervalsSize_pre st1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength (st1))) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < (Zlength (st1))) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ ((Znth j ed1 0) <= pivot_end) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < intervalsSize_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (st1)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (ed1)) = intervalsSize_pre) ” 
  &&  “ (pivot_end = (Znth high_pre ed1 0)) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end ) ”
  &&  (IntArray.full st_pre (Zlength (st1)) st1 )
  **  (IntArray.full ed_pre (Zlength (st1)) ed1 )
.

Definition partition_intervals_partial_solve_wit_3 := partition_intervals_partial_solve_wit_3_pure -> partition_intervals_partial_solve_wit_3_aux.

Definition partition_intervals_partial_solve_wit_4_pure := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (j >= high_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1 ) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : ((Zlength (st1)) = intervalsSize_pre)) (PreH9 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1 0))) (PreH11 : (PairIntervals st1 ed1 ps1 )) (PreH12 : (IntervalBounds ps1 )) (PreH13 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_end" ) )) # Int  |-> pivot_end)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength (st1))) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < (Zlength (st1))) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ”
.

Definition partition_intervals_partial_solve_wit_4_aux := 
forall (high_pre: Z) (low_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot_end: Z) (j: Z) (i: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (j >= high_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1 ) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : ((Zlength (st1)) = intervalsSize_pre)) (PreH9 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1 0))) (PreH11 : (PairIntervals st1 ed1 ps1 )) (PreH12 : (IntervalBounds ps1 )) (PreH13 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (Zlength (st1))) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < (Zlength (st1))) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < intervalsSize_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (st1)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (ed1)) = intervalsSize_pre) ” 
  &&  “ (pivot_end = (Znth high_pre ed1 0)) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end ) ”
  &&  (IntArray.full st_pre (Zlength (st1)) st1 )
  **  (IntArray.full ed_pre (Zlength (st1)) ed1 )
.

Definition partition_intervals_partial_solve_wit_4 := partition_intervals_partial_solve_wit_4_pure -> partition_intervals_partial_solve_wit_4_aux.

(*----- Function quicksort_intervals_range -----*)

Definition quicksort_intervals_range_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (PairIntervals st1 ed1 ps1 )) (PreH5 : (IntervalBounds ps1 )) (PreH6 : (IntervalPermutation ps ps1 )) (PreH7 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH8 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= intervalsSize_pre)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < intervalsSize_pre)) (PreH14 : (PairIntervals st_l ed_l ps )) (PreH15 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_intervals_range_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (PairIntervals st1 ed1 ps1 )) (PreH5 : (IntervalBounds ps1 )) (PreH6 : (IntervalPermutation ps ps1 )) (PreH7 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH8 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= intervalsSize_pre)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < intervalsSize_pre)) (PreH14 : (PairIntervals st_l ed_l ps )) (PreH15 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_intervals_range_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (PreH1 : (pivot < right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps )) (PreH9 : (IntervalBounds current_ps )) (PreH10 : (IntervalPermutation ps current_ps )) (PreH11 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH12 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH13 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
|--
  “ ((pivot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot + 1 )) ”
.

Definition quicksort_intervals_range_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (PreH1 : (pivot < right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps )) (PreH9 : (IntervalBounds current_ps )) (PreH10 : (IntervalPermutation ps current_ps )) (PreH11 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH12 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH13 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_intervals_range_entail_wit_1_1 := 
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation ps1 ps1_2 )) (PreH4 : (IntervalSameOutsideRange ps1 ps1_2 left_pre (retval - 1 ) )) (PreH5 : (IntervalsEndSortedRange ps1_2 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (PairIntervals st1 ed1 ps1 )) (PreH10 : (IntervalBounds ps1 )) (PreH11 : (IntervalPermutation ps ps1 )) (PreH12 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH13 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= intervalsSize_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < intervalsSize_pre)) (PreH19 : (PairIntervals st_l ed_l ps )) (PreH20 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1_2 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1_2 )
|--
  EX (current_st: (@list Z))  (current_ed: (@list Z))  (current_ps: (@list interval)) ,
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (PairIntervals current_st current_ed current_ps ) ” 
  &&  “ (IntervalBounds current_ps ) ” 
  &&  “ (IntervalPermutation ps current_ps ) ” 
  &&  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre ) ” 
  &&  “ (IntervalPartitionedAt current_ps left_pre right_pre retval ) ” 
  &&  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1 ) ) ”
  &&  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
) \/
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation ps1 ps1_2 )) (PreH4 : (IntervalSameOutsideRange ps1 ps1_2 left_pre (retval - 1 ) )) (PreH5 : (IntervalsEndSortedRange ps1_2 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (PairIntervals st1 ed1 ps1 )) (PreH10 : (IntervalBounds ps1 )) (PreH11 : (IntervalPermutation ps ps1 )) (PreH12 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH13 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= intervalsSize_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < intervalsSize_pre)) (PreH19 : (PairIntervals st_l ed_l ps )) (PreH20 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (current_ps: (@list interval)) ,
  “ (PairIntervals st1_2 ed1_2 current_ps ) ” 
  &&  “ (IntervalBounds current_ps ) ” 
  &&  “ (IntervalPermutation ps current_ps ) ” 
  &&  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre ) ” 
  &&  “ (IntervalPartitionedAt current_ps left_pre right_pre retval ) ” 
  &&  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1 ) ) ”
  &&  emp
).

Definition quicksort_intervals_range_entail_wit_1_2 := 
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (retval <= left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (PairIntervals st1 ed1 ps1 )) (PreH5 : (IntervalBounds ps1 )) (PreH6 : (IntervalPermutation ps ps1 )) (PreH7 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH8 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= intervalsSize_pre)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < intervalsSize_pre)) (PreH14 : (PairIntervals st_l ed_l ps )) (PreH15 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  EX (current_st: (@list Z))  (current_ed: (@list Z))  (current_ps: (@list interval)) ,
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (PairIntervals current_st current_ed current_ps ) ” 
  &&  “ (IntervalBounds current_ps ) ” 
  &&  “ (IntervalPermutation ps current_ps ) ” 
  &&  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre ) ” 
  &&  “ (IntervalPartitionedAt current_ps left_pre right_pre retval ) ” 
  &&  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1 ) ) ”
  &&  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
) \/
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (retval <= left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (PairIntervals st1 ed1 ps1 )) (PreH5 : (IntervalBounds ps1 )) (PreH6 : (IntervalPermutation ps ps1 )) (PreH7 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH8 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= intervalsSize_pre)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < intervalsSize_pre)) (PreH14 : (PairIntervals st_l ed_l ps )) (PreH15 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (current_ps: (@list interval)) ,
  “ (PairIntervals st1 ed1 current_ps ) ” 
  &&  “ (IntervalBounds current_ps ) ” 
  &&  “ (IntervalPermutation ps current_ps ) ” 
  &&  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre ) ” 
  &&  “ (IntervalPartitionedAt current_ps left_pre right_pre retval ) ” 
  &&  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1 ) ) ”
  &&  emp
).

Definition quicksort_intervals_range_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation current_ps ps1_2 )) (PreH4 : (IntervalSameOutsideRange current_ps ps1_2 (pivot + 1 ) right_pre )) (PreH5 : (IntervalsEndSortedRange ps1_2 (pivot + 1 ) right_pre )) (PreH6 : (pivot < right_pre)) (PreH7 : (0 <= intervalsSize_pre)) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre < right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (left_pre <= pivot)) (PreH12 : (pivot <= right_pre)) (PreH13 : (PairIntervals current_st current_ed current_ps )) (PreH14 : (IntervalBounds current_ps )) (PreH15 : (IntervalPermutation ps current_ps )) (PreH16 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH17 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH18 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  (IntArray.full st_pre intervalsSize_pre st1_2 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1_2 )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre ) ” 
  &&  “ (IntervalsEndSortedRange ps1 left_pre right_pre ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation current_ps ps1_2 )) (PreH4 : (IntervalSameOutsideRange current_ps ps1_2 (pivot + 1 ) right_pre )) (PreH5 : (IntervalsEndSortedRange ps1_2 (pivot + 1 ) right_pre )) (PreH6 : (pivot < right_pre)) (PreH7 : (0 <= intervalsSize_pre)) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre < right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (left_pre <= pivot)) (PreH12 : (pivot <= right_pre)) (PreH13 : (PairIntervals current_st current_ed current_ps )) (PreH14 : (IntervalBounds current_ps )) (PreH15 : (IntervalPermutation ps current_ps )) (PreH16 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH17 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH18 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (PairIntervals st1_2 ed1_2 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre ) ” 
  &&  “ (IntervalsEndSortedRange ps1 left_pre right_pre ) ”
  &&  emp
).

Definition quicksort_intervals_range_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (PreH1 : (pivot >= right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps )) (PreH9 : (IntervalBounds current_ps )) (PreH10 : (IntervalPermutation ps current_ps )) (PreH11 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH12 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH13 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre ) ” 
  &&  “ (IntervalsEndSortedRange ps1 left_pre right_pre ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (PreH1 : (pivot >= right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps )) (PreH9 : (IntervalBounds current_ps )) (PreH10 : (IntervalPermutation ps current_ps )) (PreH11 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH12 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH13 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (PairIntervals current_st current_ed ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre ) ” 
  &&  “ (IntervalsEndSortedRange ps1 left_pre right_pre ) ”
  &&  emp
).

Definition quicksort_intervals_range_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps )) (PreH7 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre ) ” 
  &&  “ (IntervalsEndSortedRange ps1 left_pre right_pre ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps )) (PreH7 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (PairIntervals st_l ed_l ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre ) ” 
  &&  “ (IntervalsEndSortedRange ps1 left_pre right_pre ) ”
  &&  emp
).

Definition quicksort_intervals_range_partial_solve_wit_1_pure := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps )) (PreH7 : (IntervalBounds ps )) ,
  ((( &( "pivot" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
.

Definition quicksort_intervals_range_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps )) (PreH7 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
.

Definition quicksort_intervals_range_partial_solve_wit_1 := quicksort_intervals_range_partial_solve_wit_1_pure -> quicksort_intervals_range_partial_solve_wit_1_aux.

Definition quicksort_intervals_range_partial_solve_wit_2_pure := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (PairIntervals st1 ed1 ps1 )) (PreH5 : (IntervalBounds ps1 )) (PreH6 : (IntervalPermutation ps ps1 )) (PreH7 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH8 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= intervalsSize_pre)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < intervalsSize_pre)) (PreH14 : (PairIntervals st_l ed_l ps )) (PreH15 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "pivot" ) )) # Int  |-> retval)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < intervalsSize_pre) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ”
.

Definition quicksort_intervals_range_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (retval: Z) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (PairIntervals st1 ed1 ps1 )) (PreH5 : (IntervalBounds ps1 )) (PreH6 : (IntervalPermutation ps ps1 )) (PreH7 : (IntervalSameOutsideRange ps ps1 left_pre right_pre )) (PreH8 : (IntervalPartitionedAt ps1 left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= intervalsSize_pre)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < intervalsSize_pre)) (PreH14 : (PairIntervals st_l ed_l ps )) (PreH15 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < intervalsSize_pre) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre ) ” 
  &&  “ (IntervalPartitionedAt ps1 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
.

Definition quicksort_intervals_range_partial_solve_wit_2 := quicksort_intervals_range_partial_solve_wit_2_pure -> quicksort_intervals_range_partial_solve_wit_2_aux.

Definition quicksort_intervals_range_partial_solve_wit_3_pure := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (PreH1 : (pivot < right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps )) (PreH9 : (IntervalBounds current_ps )) (PreH10 : (IntervalPermutation ps current_ps )) (PreH11 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH12 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH13 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (PairIntervals current_st current_ed current_ps ) ” 
  &&  “ (IntervalBounds current_ps ) ”
.

Definition quicksort_intervals_range_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (pivot: Z) (current_st: (@list Z)) (current_ed: (@list Z)) (current_ps: (@list interval)) (PreH1 : (pivot < right_pre)) (PreH2 : (0 <= intervalsSize_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps )) (PreH9 : (IntervalBounds current_ps )) (PreH10 : (IntervalPermutation ps current_ps )) (PreH11 : (IntervalSameOutsideRange ps current_ps left_pre right_pre )) (PreH12 : (IntervalPartitionedAt current_ps left_pre right_pre pivot )) (PreH13 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) )) ,
  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (PairIntervals current_st current_ed current_ps ) ” 
  &&  “ (IntervalBounds current_ps ) ” 
  &&  “ (pivot < right_pre) ” 
  &&  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (right_pre < intervalsSize_pre) ” 
  &&  “ (left_pre <= pivot) ” 
  &&  “ (pivot <= right_pre) ” 
  &&  “ (PairIntervals current_st current_ed current_ps ) ” 
  &&  “ (IntervalBounds current_ps ) ” 
  &&  “ (IntervalPermutation ps current_ps ) ” 
  &&  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre ) ” 
  &&  “ (IntervalPartitionedAt current_ps left_pre right_pre pivot ) ” 
  &&  “ (IntervalsEndSortedRange current_ps left_pre (pivot - 1 ) ) ”
  &&  (IntArray.full st_pre intervalsSize_pre current_st )
  **  (IntArray.full ed_pre intervalsSize_pre current_ed )
.

Definition quicksort_intervals_range_partial_solve_wit_3 := quicksort_intervals_range_partial_solve_wit_3_pure -> quicksort_intervals_range_partial_solve_wit_3_aux.

(*----- Function quicksort_intervals -----*)

Definition quicksort_intervals_safety_wit_1 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps )) (PreH4 : (IntervalBounds ps )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ ((intervalsSize_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (intervalsSize_pre - 1 )) ”
.

Definition quicksort_intervals_safety_wit_2 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps )) (PreH4 : (IntervalBounds ps )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_intervals_safety_wit_3 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps )) (PreH4 : (IntervalBounds ps )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_intervals_return_wit_1 := 
(
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation ps ps1_2 )) (PreH4 : (IntervalSameOutsideRange ps ps1_2 0 (intervalsSize_pre - 1 ) )) (PreH5 : (IntervalsEndSortedRange ps1_2 0 (intervalsSize_pre - 1 ) )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1_2 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1_2 )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalsEndSorted ps1 ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (intervalsSize_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH2 : (IntervalBounds ps1_2 )) (PreH3 : (IntervalPermutation ps ps1_2 )) (PreH4 : (IntervalSameOutsideRange ps ps1_2 0 (intervalsSize_pre - 1 ) )) (PreH5 : (IntervalsEndSortedRange ps1_2 0 (intervalsSize_pre - 1 ) )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (PairIntervals st1_2 ed1_2 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalsEndSorted ps1 ) ”
  &&  emp
).

Definition quicksort_intervals_partial_solve_wit_1_pure := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps )) (PreH4 : (IntervalBounds ps )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (intervalsSize_pre - 1 )) ” 
  &&  “ ((intervalsSize_pre - 1 ) < intervalsSize_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
.

Definition quicksort_intervals_partial_solve_wit_1_aux := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps )) (PreH4 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (intervalsSize_pre - 1 )) ” 
  &&  “ ((intervalsSize_pre - 1 ) < intervalsSize_pre) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ” 
  &&  “ (0 <= intervalsSize_pre) ” 
  &&  “ (intervalsSize_pre <= 1000) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
.

Definition quicksort_intervals_partial_solve_wit_1 := quicksort_intervals_partial_solve_wit_1_pure -> quicksort_intervals_partial_solve_wit_1_aux.

(*----- Function eraseOverlapIntervals -----*)

Definition eraseOverlapIntervals_safety_wit_1 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (PairIntervals st1 ed1 ps1 )) (PreH2 : (IntervalBounds ps1 )) (PreH3 : (IntervalPermutation ps ps1 )) (PreH4 : (IntervalsEndSorted ps1 )) (PreH5 : (0 <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps )) (PreH8 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eraseOverlapIntervals_safety_wit_2 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (intervalsSize_pre = 0)) (PreH2 : (PairIntervals st1 ed1 ps1 )) (PreH3 : (IntervalBounds ps1 )) (PreH4 : (IntervalPermutation ps ps1 )) (PreH5 : (IntervalsEndSorted ps1 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eraseOverlapIntervals_safety_wit_3 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (intervalsSize_pre <> 0)) (PreH2 : (PairIntervals st1 ed1 ps1 )) (PreH3 : (IntervalBounds ps1 )) (PreH4 : (IntervalPermutation ps ps1 )) (PreH5 : (IntervalsEndSorted ps1 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  ((( &( "kept" ) )) # Int  |->_)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eraseOverlapIntervals_safety_wit_4 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (intervalsSize_pre <> 0)) (PreH2 : (PairIntervals st1 ed1 ps1 )) (PreH3 : (IntervalBounds ps1 )) (PreH4 : (IntervalPermutation ps ps1 )) (PreH5 : (IntervalsEndSorted ps1 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  ((( &( "last_end" ) )) # Int  |->_)
  **  ((( &( "kept" ) )) # Int  |-> 1)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eraseOverlapIntervals_safety_wit_5 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (intervalsSize_pre <> 0)) (PreH2 : (PairIntervals st1 ed1 ps1 )) (PreH3 : (IntervalBounds ps1 )) (PreH4 : (IntervalPermutation ps ps1 )) (PreH5 : (IntervalsEndSorted ps1 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "last_end" ) )) # Int  |-> (Znth 0 ed1 0))
  **  ((( &( "kept" ) )) # Int  |-> 1)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eraseOverlapIntervals_safety_wit_6 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps: (@list interval)) (sorted_ed: (@list Z)) (sorted_st: (@list Z)) (last_end: Z) (kept: Z) (i: Z) (PreH1 : ((Znth i sorted_st 0) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : ((-10000) <= last_end)) (PreH8 : (last_end <= 10000)) (PreH9 : ((Zlength (sorted_st)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH12 : (IntervalBounds sorted_ps )) (PreH13 : (IntervalPermutation ps sorted_ps )) (PreH14 : (IntervalsEndSorted sorted_ps )) (PreH15 : (GreedyPrefixState sorted_ps i kept last_end )) ,
  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "last_end" ) )) # Int  |-> last_end)
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
|--
  “ ((kept + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (kept + 1 )) ”
.

Definition eraseOverlapIntervals_safety_wit_7 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps: (@list interval)) (sorted_ed: (@list Z)) (sorted_st: (@list Z)) (last_end: Z) (kept: Z) (i: Z) (PreH1 : ((Znth i sorted_st 0) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : ((-10000) <= last_end)) (PreH8 : (last_end <= 10000)) (PreH9 : ((Zlength (sorted_st)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH12 : (IntervalBounds sorted_ps )) (PreH13 : (IntervalPermutation ps sorted_ps )) (PreH14 : (IntervalsEndSorted sorted_ps )) (PreH15 : (GreedyPrefixState sorted_ps i kept last_end )) ,
  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
  **  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> (kept + 1 ))
  **  ((( &( "last_end" ) )) # Int  |-> (Znth i sorted_ed 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eraseOverlapIntervals_safety_wit_8 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps: (@list interval)) (sorted_ed: (@list Z)) (sorted_st: (@list Z)) (last_end: Z) (kept: Z) (i: Z) (PreH1 : ((Znth i sorted_st 0) < last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : ((-10000) <= last_end)) (PreH8 : (last_end <= 10000)) (PreH9 : ((Zlength (sorted_st)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH12 : (IntervalBounds sorted_ps )) (PreH13 : (IntervalPermutation ps sorted_ps )) (PreH14 : (IntervalsEndSorted sorted_ps )) (PreH15 : (GreedyPrefixState sorted_ps i kept last_end )) ,
  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "last_end" ) )) # Int  |-> last_end)
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eraseOverlapIntervals_safety_wit_9 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_st: (@list Z)) (sorted_ed: (@list Z)) (sorted_ps: (@list interval)) (kept: Z) (last_end: Z) (PreH1 : (1 <= kept)) (PreH2 : (kept <= intervalsSize_pre)) (PreH3 : (0 <= (intervalsSize_pre - kept ))) (PreH4 : ((intervalsSize_pre - kept ) <= intervalsSize_pre)) (PreH5 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH6 : (IntervalBounds sorted_ps )) (PreH7 : (IntervalPermutation ps sorted_ps )) (PreH8 : (IntervalsEndSorted sorted_ps )) (PreH9 : (GreedyPrefixState sorted_ps intervalsSize_pre kept last_end )) (PreH10 : (MinimumRemovals ps (intervalsSize_pre - kept ) )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "last_end" ) )) # Int  |-> last_end)
  **  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
|--
  “ ((intervalsSize_pre - kept ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (intervalsSize_pre - kept )) ”
.

Definition eraseOverlapIntervals_entail_wit_1 := 
(
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (intervalsSize_pre <> 0)) (PreH2 : (PairIntervals st1 ed1 ps1 )) (PreH3 : (IntervalBounds ps1 )) (PreH4 : (IntervalPermutation ps ps1 )) (PreH5 : (IntervalsEndSorted ps1 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  ((( &( "i" ) )) # Int  |-> 1)
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
  **  ((( &( "last_end" ) )) # Int  |-> (Znth 0 ed1 0))
  **  ((( &( "kept" ) )) # Int  |-> 1)
  **  (IntArray.full st_pre intervalsSize_pre st1 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
|--
  EX (sorted_ps: (@list interval))  (sorted_ed: (@list Z))  (sorted_st: (@list Z))  (last_end: Z)  (kept: Z)  (i: Z) ,
  “ (1 <= i) ” 
  &&  “ (i <= intervalsSize_pre) ” 
  &&  “ (1 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ ((-10000) <= last_end) ” 
  &&  “ (last_end <= 10000) ” 
  &&  “ ((Zlength (sorted_st)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (sorted_ed)) = intervalsSize_pre) ” 
  &&  “ (PairIntervals sorted_st sorted_ed sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps i kept last_end ) ”
  &&  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "last_end" ) )) # Int  |-> last_end)
  **  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
) \/
(
forall (intervalsSize_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : ((Zlength (st1)) = intervalsSize_pre)) (PreH2 : ((Zlength (ed1)) = intervalsSize_pre)) (PreH3 : (intervalsSize_pre <> 0)) (PreH4 : (PairIntervals st1 ed1 ps1 )) (PreH5 : (IntervalBounds ps1 )) (PreH6 : (IntervalPermutation ps ps1 )) (PreH7 : (IntervalsEndSorted ps1 )) (PreH8 : (0 <= intervalsSize_pre)) (PreH9 : (intervalsSize_pre <= 1000)) (PreH10 : (PairIntervals st_l ed_l ps )) (PreH11 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (sorted_ps: (@list interval)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= (Zlength (st1))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((-10000) <= (Znth 0 ed1 0)) ” 
  &&  “ ((Znth 0 ed1 0) <= 10000) ” 
  &&  “ (PairIntervals st1 ed1 sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps 1 1 (Znth 0 ed1 0) ) ”
  &&  emp
).

Definition eraseOverlapIntervals_entail_wit_2_1 := 
(
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps_2: (@list interval)) (sorted_ed_2: (@list Z)) (sorted_st_2: (@list Z)) (last_end_2: Z) (kept_2: Z) (i_2: Z) (PreH1 : ((Znth i_2 sorted_st_2 0) >= last_end_2)) (PreH2 : (i_2 < intervalsSize_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= intervalsSize_pre)) (PreH5 : (1 <= kept_2)) (PreH6 : (kept_2 <= i_2)) (PreH7 : ((-10000) <= last_end_2)) (PreH8 : (last_end_2 <= 10000)) (PreH9 : ((Zlength (sorted_st_2)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed_2)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 )) (PreH12 : (IntervalBounds sorted_ps_2 )) (PreH13 : (IntervalPermutation ps sorted_ps_2 )) (PreH14 : (IntervalsEndSorted sorted_ps_2 )) (PreH15 : (GreedyPrefixState sorted_ps_2 i_2 kept_2 last_end_2 )) ,
  (IntArray.full ed_pre intervalsSize_pre sorted_ed_2 )
  **  (IntArray.full st_pre intervalsSize_pre sorted_st_2 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "kept" ) )) # Int  |-> (kept_2 + 1 ))
  **  ((( &( "last_end" ) )) # Int  |-> (Znth i_2 sorted_ed_2 0))
|--
  EX (sorted_ps: (@list interval))  (sorted_ed: (@list Z))  (sorted_st: (@list Z))  (last_end: Z)  (kept: Z)  (i: Z) ,
  “ (1 <= i) ” 
  &&  “ (i <= intervalsSize_pre) ” 
  &&  “ (1 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ ((-10000) <= last_end) ” 
  &&  “ (last_end <= 10000) ” 
  &&  “ ((Zlength (sorted_st)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (sorted_ed)) = intervalsSize_pre) ” 
  &&  “ (PairIntervals sorted_st sorted_ed sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps i kept last_end ) ”
  &&  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "last_end" ) )) # Int  |-> last_end)
  **  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
) \/
(
forall (intervalsSize_pre: Z) (ps: (@list interval)) (sorted_ps_2: (@list interval)) (sorted_ed_2: (@list Z)) (sorted_st_2: (@list Z)) (last_end_2: Z) (kept_2: Z) (i_2: Z) (PreH1 : ((Znth i_2 sorted_st_2 0) >= last_end_2)) (PreH2 : (i_2 < intervalsSize_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= intervalsSize_pre)) (PreH5 : (1 <= kept_2)) (PreH6 : (kept_2 <= i_2)) (PreH7 : ((-10000) <= last_end_2)) (PreH8 : (last_end_2 <= 10000)) (PreH9 : ((Zlength (sorted_st_2)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed_2)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 )) (PreH12 : (IntervalBounds sorted_ps_2 )) (PreH13 : (IntervalPermutation ps sorted_ps_2 )) (PreH14 : (IntervalsEndSorted sorted_ps_2 )) (PreH15 : (GreedyPrefixState sorted_ps_2 i_2 kept_2 last_end_2 )) ,
  TT && emp 
|--
  EX (sorted_ps: (@list interval)) ,
  “ (1 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= (Zlength (sorted_st_2))) ” 
  &&  “ (1 <= (kept_2 + 1 )) ” 
  &&  “ ((kept_2 + 1 ) <= (i_2 + 1 )) ” 
  &&  “ ((-10000) <= (Znth i_2 sorted_ed_2 0)) ” 
  &&  “ ((Znth i_2 sorted_ed_2 0) <= 10000) ” 
  &&  “ (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps (i_2 + 1 ) (kept_2 + 1 ) (Znth i_2 sorted_ed_2 0) ) ”
  &&  emp
).

Definition eraseOverlapIntervals_entail_wit_2_2 := 
(
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps_2: (@list interval)) (sorted_ed_2: (@list Z)) (sorted_st_2: (@list Z)) (last_end_2: Z) (kept_2: Z) (i_2: Z) (PreH1 : ((Znth i_2 sorted_st_2 0) < last_end_2)) (PreH2 : (i_2 < intervalsSize_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= intervalsSize_pre)) (PreH5 : (1 <= kept_2)) (PreH6 : (kept_2 <= i_2)) (PreH7 : ((-10000) <= last_end_2)) (PreH8 : (last_end_2 <= 10000)) (PreH9 : ((Zlength (sorted_st_2)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed_2)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 )) (PreH12 : (IntervalBounds sorted_ps_2 )) (PreH13 : (IntervalPermutation ps sorted_ps_2 )) (PreH14 : (IntervalsEndSorted sorted_ps_2 )) (PreH15 : (GreedyPrefixState sorted_ps_2 i_2 kept_2 last_end_2 )) ,
  (IntArray.full st_pre intervalsSize_pre sorted_st_2 )
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "kept" ) )) # Int  |-> kept_2)
  **  ((( &( "last_end" ) )) # Int  |-> last_end_2)
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed_2 )
|--
  EX (sorted_ps: (@list interval))  (sorted_ed: (@list Z))  (sorted_st: (@list Z))  (last_end: Z)  (kept: Z)  (i: Z) ,
  “ (1 <= i) ” 
  &&  “ (i <= intervalsSize_pre) ” 
  &&  “ (1 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ ((-10000) <= last_end) ” 
  &&  “ (last_end <= 10000) ” 
  &&  “ ((Zlength (sorted_st)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (sorted_ed)) = intervalsSize_pre) ” 
  &&  “ (PairIntervals sorted_st sorted_ed sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps i kept last_end ) ”
  &&  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "last_end" ) )) # Int  |-> last_end)
  **  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
) \/
(
forall (intervalsSize_pre: Z) (ps: (@list interval)) (sorted_ps_2: (@list interval)) (sorted_ed_2: (@list Z)) (sorted_st_2: (@list Z)) (last_end_2: Z) (kept_2: Z) (i_2: Z) (PreH1 : ((Znth i_2 sorted_st_2 0) < last_end_2)) (PreH2 : (i_2 < intervalsSize_pre)) (PreH3 : (1 <= i_2)) (PreH4 : (i_2 <= intervalsSize_pre)) (PreH5 : (1 <= kept_2)) (PreH6 : (kept_2 <= i_2)) (PreH7 : ((-10000) <= last_end_2)) (PreH8 : (last_end_2 <= 10000)) (PreH9 : ((Zlength (sorted_st_2)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed_2)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 )) (PreH12 : (IntervalBounds sorted_ps_2 )) (PreH13 : (IntervalPermutation ps sorted_ps_2 )) (PreH14 : (IntervalsEndSorted sorted_ps_2 )) (PreH15 : (GreedyPrefixState sorted_ps_2 i_2 kept_2 last_end_2 )) ,
  TT && emp 
|--
  EX (sorted_ps: (@list interval)) ,
  “ (1 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= (Zlength (sorted_st_2))) ” 
  &&  “ (kept_2 <= (i_2 + 1 )) ” 
  &&  “ (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps (i_2 + 1 ) kept_2 last_end_2 ) ”
  &&  emp
).

Definition eraseOverlapIntervals_entail_wit_3 := 
(
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps_2: (@list interval)) (sorted_ed_2: (@list Z)) (sorted_st_2: (@list Z)) (last_end: Z) (kept: Z) (i: Z) (PreH1 : (i >= intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : ((-10000) <= last_end)) (PreH7 : (last_end <= 10000)) (PreH8 : ((Zlength (sorted_st_2)) = intervalsSize_pre)) (PreH9 : ((Zlength (sorted_ed_2)) = intervalsSize_pre)) (PreH10 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 )) (PreH11 : (IntervalBounds sorted_ps_2 )) (PreH12 : (IntervalPermutation ps sorted_ps_2 )) (PreH13 : (IntervalsEndSorted sorted_ps_2 )) (PreH14 : (GreedyPrefixState sorted_ps_2 i kept last_end )) ,
  (IntArray.full st_pre intervalsSize_pre sorted_st_2 )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed_2 )
|--
  EX (sorted_st: (@list Z))  (sorted_ed: (@list Z))  (sorted_ps: (@list interval)) ,
  “ (1 <= kept) ” 
  &&  “ (kept <= intervalsSize_pre) ” 
  &&  “ (0 <= (intervalsSize_pre - kept )) ” 
  &&  “ ((intervalsSize_pre - kept ) <= intervalsSize_pre) ” 
  &&  “ (PairIntervals sorted_st sorted_ed sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps intervalsSize_pre kept last_end ) ” 
  &&  “ (MinimumRemovals ps (intervalsSize_pre - kept ) ) ”
  &&  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
) \/
(
forall (intervalsSize_pre: Z) (ps: (@list interval)) (sorted_ps_2: (@list interval)) (sorted_ed_2: (@list Z)) (sorted_st_2: (@list Z)) (last_end: Z) (kept: Z) (i: Z) (PreH1 : (i >= intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : ((-10000) <= last_end)) (PreH7 : (last_end <= 10000)) (PreH8 : ((Zlength (sorted_st_2)) = intervalsSize_pre)) (PreH9 : ((Zlength (sorted_ed_2)) = intervalsSize_pre)) (PreH10 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2 )) (PreH11 : (IntervalBounds sorted_ps_2 )) (PreH12 : (IntervalPermutation ps sorted_ps_2 )) (PreH13 : (IntervalsEndSorted sorted_ps_2 )) (PreH14 : (GreedyPrefixState sorted_ps_2 i kept last_end )) ,
  TT && emp 
|--
  EX (sorted_ps: (@list interval)) ,
  “ (kept <= (Zlength (sorted_st_2))) ” 
  &&  “ (0 <= ((Zlength (sorted_st_2)) - kept )) ” 
  &&  “ (((Zlength (sorted_st_2)) - kept ) <= (Zlength (sorted_st_2))) ” 
  &&  “ (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps (Zlength (sorted_st_2)) kept last_end ) ” 
  &&  “ (MinimumRemovals ps ((Zlength (sorted_st_2)) - kept ) ) ”
  &&  emp
).

Definition eraseOverlapIntervals_return_wit_1 := 
(
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_st: (@list Z)) (sorted_ed: (@list Z)) (sorted_ps: (@list interval)) (kept: Z) (last_end: Z) (PreH1 : (1 <= kept)) (PreH2 : (kept <= intervalsSize_pre)) (PreH3 : (0 <= (intervalsSize_pre - kept ))) (PreH4 : ((intervalsSize_pre - kept ) <= intervalsSize_pre)) (PreH5 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH6 : (IntervalBounds sorted_ps )) (PreH7 : (IntervalPermutation ps sorted_ps )) (PreH8 : (IntervalsEndSorted sorted_ps )) (PreH9 : (GreedyPrefixState sorted_ps intervalsSize_pre kept last_end )) (PreH10 : (MinimumRemovals ps (intervalsSize_pre - kept ) )) ,
  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (0 <= (intervalsSize_pre - kept )) ” 
  &&  “ ((intervalsSize_pre - kept ) <= intervalsSize_pre) ” 
  &&  “ (MinimumRemovals ps (intervalsSize_pre - kept ) ) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalsEndSorted ps1 ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (intervalsSize_pre: Z) (ps: (@list interval)) (sorted_st: (@list Z)) (sorted_ed: (@list Z)) (sorted_ps: (@list interval)) (kept: Z) (last_end: Z) (PreH1 : (1 <= kept)) (PreH2 : (kept <= intervalsSize_pre)) (PreH3 : (0 <= (intervalsSize_pre - kept ))) (PreH4 : ((intervalsSize_pre - kept ) <= intervalsSize_pre)) (PreH5 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH6 : (IntervalBounds sorted_ps )) (PreH7 : (IntervalPermutation ps sorted_ps )) (PreH8 : (IntervalsEndSorted sorted_ps )) (PreH9 : (GreedyPrefixState sorted_ps intervalsSize_pre kept last_end )) (PreH10 : (MinimumRemovals ps (intervalsSize_pre - kept ) )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (PairIntervals sorted_st sorted_ed ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalsEndSorted ps1 ) ”
  &&  emp
).

Definition eraseOverlapIntervals_return_wit_2 := 
(
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (intervalsSize_pre = 0)) (PreH2 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH3 : (IntervalBounds ps1_2 )) (PreH4 : (IntervalPermutation ps ps1_2 )) (PreH5 : (IntervalsEndSorted ps1_2 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1_2 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1_2 )
|--
  EX (st1: (@list Z))  (ed1: (@list Z))  (ps1: (@list interval)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= intervalsSize_pre) ” 
  &&  “ (MinimumRemovals ps 0 ) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalsEndSorted ps1 ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
) \/
(
forall (intervalsSize_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1_2: (@list Z)) (ed1_2: (@list Z)) (ps1_2: (@list interval)) (PreH1 : (intervalsSize_pre = 0)) (PreH2 : (PairIntervals st1_2 ed1_2 ps1_2 )) (PreH3 : (IntervalBounds ps1_2 )) (PreH4 : (IntervalPermutation ps ps1_2 )) (PreH5 : (IntervalsEndSorted ps1_2 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  TT && emp 
|--
  EX (ps1: (@list interval)) ,
  “ (0 <= 0) ” 
  &&  “ (MinimumRemovals ps 0 ) ” 
  &&  “ (PairIntervals st1_2 ed1_2 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalsEndSorted ps1 ) ”
  &&  emp
).

Definition eraseOverlapIntervals_partial_solve_wit_1_pure := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps )) (PreH4 : (IntervalBounds ps )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "ed" ) )) # Ptr  |-> ed_pre)
  **  ((( &( "intervalsSize" ) )) # Int  |-> intervalsSize_pre)
  **  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (intervalsSize_pre <= 1000) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
.

Definition eraseOverlapIntervals_partial_solve_wit_1_aux := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (PreH1 : (0 <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps )) (PreH4 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
|--
  “ (0 <= intervalsSize_pre) ” 
  &&  “ (intervalsSize_pre <= 1000) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ” 
  &&  “ (0 <= intervalsSize_pre) ” 
  &&  “ (intervalsSize_pre <= 1000) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (IntArray.full st_pre intervalsSize_pre st_l )
  **  (IntArray.full ed_pre intervalsSize_pre ed_l )
.

Definition eraseOverlapIntervals_partial_solve_wit_1 := eraseOverlapIntervals_partial_solve_wit_1_pure -> eraseOverlapIntervals_partial_solve_wit_1_aux.

Definition eraseOverlapIntervals_partial_solve_wit_2 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (ed_l: (@list Z)) (st_l: (@list Z)) (st1: (@list Z)) (ed1: (@list Z)) (ps1: (@list interval)) (PreH1 : (intervalsSize_pre <> 0)) (PreH2 : (PairIntervals st1 ed1 ps1 )) (PreH3 : (IntervalBounds ps1 )) (PreH4 : (IntervalPermutation ps ps1 )) (PreH5 : (IntervalsEndSorted ps1 )) (PreH6 : (0 <= intervalsSize_pre)) (PreH7 : (intervalsSize_pre <= 1000)) (PreH8 : (PairIntervals st_l ed_l ps )) (PreH9 : (IntervalBounds ps )) ,
  (IntArray.full st_pre intervalsSize_pre st1 )
  **  (IntArray.full ed_pre intervalsSize_pre ed1 )
|--
  “ (intervalsSize_pre <> 0) ” 
  &&  “ (PairIntervals st1 ed1 ps1 ) ” 
  &&  “ (IntervalBounds ps1 ) ” 
  &&  “ (IntervalPermutation ps ps1 ) ” 
  &&  “ (IntervalsEndSorted ps1 ) ” 
  &&  “ (0 <= intervalsSize_pre) ” 
  &&  “ (intervalsSize_pre <= 1000) ” 
  &&  “ (PairIntervals st_l ed_l ps ) ” 
  &&  “ (IntervalBounds ps ) ”
  &&  (((ed_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 ed1 0))
  **  (IntArray.missing_i ed_pre 0 0 intervalsSize_pre ed1 )
  **  (IntArray.full st_pre intervalsSize_pre st1 )
.

Definition eraseOverlapIntervals_partial_solve_wit_3 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps: (@list interval)) (sorted_ed: (@list Z)) (sorted_st: (@list Z)) (last_end: Z) (kept: Z) (i: Z) (PreH1 : (i < intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : ((-10000) <= last_end)) (PreH7 : (last_end <= 10000)) (PreH8 : ((Zlength (sorted_st)) = intervalsSize_pre)) (PreH9 : ((Zlength (sorted_ed)) = intervalsSize_pre)) (PreH10 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH11 : (IntervalBounds sorted_ps )) (PreH12 : (IntervalPermutation ps sorted_ps )) (PreH13 : (IntervalsEndSorted sorted_ps )) (PreH14 : (GreedyPrefixState sorted_ps i kept last_end )) ,
  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
|--
  “ (i < intervalsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= intervalsSize_pre) ” 
  &&  “ (1 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ ((-10000) <= last_end) ” 
  &&  “ (last_end <= 10000) ” 
  &&  “ ((Zlength (sorted_st)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (sorted_ed)) = intervalsSize_pre) ” 
  &&  “ (PairIntervals sorted_st sorted_ed sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps i kept last_end ) ”
  &&  (((st_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted_st 0))
  **  (IntArray.missing_i st_pre i 0 intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
.

Definition eraseOverlapIntervals_partial_solve_wit_4 := 
forall (intervalsSize_pre: Z) (ed_pre: Z) (st_pre: Z) (ps: (@list interval)) (sorted_ps: (@list interval)) (sorted_ed: (@list Z)) (sorted_st: (@list Z)) (last_end: Z) (kept: Z) (i: Z) (PreH1 : ((Znth i sorted_st 0) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : ((-10000) <= last_end)) (PreH8 : (last_end <= 10000)) (PreH9 : ((Zlength (sorted_st)) = intervalsSize_pre)) (PreH10 : ((Zlength (sorted_ed)) = intervalsSize_pre)) (PreH11 : (PairIntervals sorted_st sorted_ed sorted_ps )) (PreH12 : (IntervalBounds sorted_ps )) (PreH13 : (IntervalPermutation ps sorted_ps )) (PreH14 : (IntervalsEndSorted sorted_ps )) (PreH15 : (GreedyPrefixState sorted_ps i kept last_end )) ,
  (IntArray.full st_pre intervalsSize_pre sorted_st )
  **  (IntArray.full ed_pre intervalsSize_pre sorted_ed )
|--
  “ ((Znth i sorted_st 0) >= last_end) ” 
  &&  “ (i < intervalsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= intervalsSize_pre) ” 
  &&  “ (1 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ ((-10000) <= last_end) ” 
  &&  “ (last_end <= 10000) ” 
  &&  “ ((Zlength (sorted_st)) = intervalsSize_pre) ” 
  &&  “ ((Zlength (sorted_ed)) = intervalsSize_pre) ” 
  &&  “ (PairIntervals sorted_st sorted_ed sorted_ps ) ” 
  &&  “ (IntervalBounds sorted_ps ) ” 
  &&  “ (IntervalPermutation ps sorted_ps ) ” 
  &&  “ (IntervalsEndSorted sorted_ps ) ” 
  &&  “ (GreedyPrefixState sorted_ps i kept last_end ) ”
  &&  (((ed_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted_ed 0))
  **  (IntArray.missing_i ed_pre i 0 intervalsSize_pre sorted_ed )
  **  (IntArray.full st_pre intervalsSize_pre sorted_st )
.

Module Type VC_Correct.


Axiom proof_of_swap_intervals_return_wit_1 : swap_intervals_return_wit_1.
Axiom proof_of_swap_intervals_partial_solve_wit_1 : swap_intervals_partial_solve_wit_1.
Axiom proof_of_swap_intervals_partial_solve_wit_2 : swap_intervals_partial_solve_wit_2.
Axiom proof_of_swap_intervals_partial_solve_wit_3 : swap_intervals_partial_solve_wit_3.
Axiom proof_of_swap_intervals_partial_solve_wit_4 : swap_intervals_partial_solve_wit_4.
Axiom proof_of_swap_intervals_partial_solve_wit_5 : swap_intervals_partial_solve_wit_5.
Axiom proof_of_swap_intervals_partial_solve_wit_6 : swap_intervals_partial_solve_wit_6.
Axiom proof_of_swap_intervals_partial_solve_wit_7 : swap_intervals_partial_solve_wit_7.
Axiom proof_of_swap_intervals_partial_solve_wit_8 : swap_intervals_partial_solve_wit_8.
Axiom proof_of_partition_intervals_safety_wit_1 : partition_intervals_safety_wit_1.
Axiom proof_of_partition_intervals_safety_wit_2 : partition_intervals_safety_wit_2.
Axiom proof_of_partition_intervals_safety_wit_3 : partition_intervals_safety_wit_3.
Axiom proof_of_partition_intervals_safety_wit_4 : partition_intervals_safety_wit_4.
Axiom proof_of_partition_intervals_safety_wit_5 : partition_intervals_safety_wit_5.
Axiom proof_of_partition_intervals_safety_wit_6 : partition_intervals_safety_wit_6.
Axiom proof_of_partition_intervals_safety_wit_7 : partition_intervals_safety_wit_7.
Axiom proof_of_partition_intervals_safety_wit_8 : partition_intervals_safety_wit_8.
Axiom proof_of_partition_intervals_safety_wit_9 : partition_intervals_safety_wit_9.
Axiom proof_of_partition_intervals_entail_wit_1 : partition_intervals_entail_wit_1.
Axiom proof_of_partition_intervals_entail_wit_2_1 : partition_intervals_entail_wit_2_1.
Axiom proof_of_partition_intervals_entail_wit_2_2 : partition_intervals_entail_wit_2_2.
Axiom proof_of_partition_intervals_return_wit_1 : partition_intervals_return_wit_1.
Axiom proof_of_partition_intervals_partial_solve_wit_1 : partition_intervals_partial_solve_wit_1.
Axiom proof_of_partition_intervals_partial_solve_wit_2 : partition_intervals_partial_solve_wit_2.
Axiom proof_of_partition_intervals_partial_solve_wit_3_pure : partition_intervals_partial_solve_wit_3_pure.
Axiom proof_of_partition_intervals_partial_solve_wit_3 : partition_intervals_partial_solve_wit_3.
Axiom proof_of_partition_intervals_partial_solve_wit_4_pure : partition_intervals_partial_solve_wit_4_pure.
Axiom proof_of_partition_intervals_partial_solve_wit_4 : partition_intervals_partial_solve_wit_4.
Axiom proof_of_quicksort_intervals_range_safety_wit_1 : quicksort_intervals_range_safety_wit_1.
Axiom proof_of_quicksort_intervals_range_safety_wit_2 : quicksort_intervals_range_safety_wit_2.
Axiom proof_of_quicksort_intervals_range_safety_wit_3 : quicksort_intervals_range_safety_wit_3.
Axiom proof_of_quicksort_intervals_range_safety_wit_4 : quicksort_intervals_range_safety_wit_4.
Axiom proof_of_quicksort_intervals_range_entail_wit_1_1 : quicksort_intervals_range_entail_wit_1_1.
Axiom proof_of_quicksort_intervals_range_entail_wit_1_2 : quicksort_intervals_range_entail_wit_1_2.
Axiom proof_of_quicksort_intervals_range_return_wit_1 : quicksort_intervals_range_return_wit_1.
Axiom proof_of_quicksort_intervals_range_return_wit_2 : quicksort_intervals_range_return_wit_2.
Axiom proof_of_quicksort_intervals_range_return_wit_3 : quicksort_intervals_range_return_wit_3.
Axiom proof_of_quicksort_intervals_range_partial_solve_wit_1_pure : quicksort_intervals_range_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_intervals_range_partial_solve_wit_1 : quicksort_intervals_range_partial_solve_wit_1.
Axiom proof_of_quicksort_intervals_range_partial_solve_wit_2_pure : quicksort_intervals_range_partial_solve_wit_2_pure.
Axiom proof_of_quicksort_intervals_range_partial_solve_wit_2 : quicksort_intervals_range_partial_solve_wit_2.
Axiom proof_of_quicksort_intervals_range_partial_solve_wit_3_pure : quicksort_intervals_range_partial_solve_wit_3_pure.
Axiom proof_of_quicksort_intervals_range_partial_solve_wit_3 : quicksort_intervals_range_partial_solve_wit_3.
Axiom proof_of_quicksort_intervals_safety_wit_1 : quicksort_intervals_safety_wit_1.
Axiom proof_of_quicksort_intervals_safety_wit_2 : quicksort_intervals_safety_wit_2.
Axiom proof_of_quicksort_intervals_safety_wit_3 : quicksort_intervals_safety_wit_3.
Axiom proof_of_quicksort_intervals_return_wit_1 : quicksort_intervals_return_wit_1.
Axiom proof_of_quicksort_intervals_partial_solve_wit_1_pure : quicksort_intervals_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_intervals_partial_solve_wit_1 : quicksort_intervals_partial_solve_wit_1.
Axiom proof_of_eraseOverlapIntervals_safety_wit_1 : eraseOverlapIntervals_safety_wit_1.
Axiom proof_of_eraseOverlapIntervals_safety_wit_2 : eraseOverlapIntervals_safety_wit_2.
Axiom proof_of_eraseOverlapIntervals_safety_wit_3 : eraseOverlapIntervals_safety_wit_3.
Axiom proof_of_eraseOverlapIntervals_safety_wit_4 : eraseOverlapIntervals_safety_wit_4.
Axiom proof_of_eraseOverlapIntervals_safety_wit_5 : eraseOverlapIntervals_safety_wit_5.
Axiom proof_of_eraseOverlapIntervals_safety_wit_6 : eraseOverlapIntervals_safety_wit_6.
Axiom proof_of_eraseOverlapIntervals_safety_wit_7 : eraseOverlapIntervals_safety_wit_7.
Axiom proof_of_eraseOverlapIntervals_safety_wit_8 : eraseOverlapIntervals_safety_wit_8.
Axiom proof_of_eraseOverlapIntervals_safety_wit_9 : eraseOverlapIntervals_safety_wit_9.
Axiom proof_of_eraseOverlapIntervals_entail_wit_1 : eraseOverlapIntervals_entail_wit_1.
Axiom proof_of_eraseOverlapIntervals_entail_wit_2_1 : eraseOverlapIntervals_entail_wit_2_1.
Axiom proof_of_eraseOverlapIntervals_entail_wit_2_2 : eraseOverlapIntervals_entail_wit_2_2.
Axiom proof_of_eraseOverlapIntervals_entail_wit_3 : eraseOverlapIntervals_entail_wit_3.
Axiom proof_of_eraseOverlapIntervals_return_wit_1 : eraseOverlapIntervals_return_wit_1.
Axiom proof_of_eraseOverlapIntervals_return_wit_2 : eraseOverlapIntervals_return_wit_2.
Axiom proof_of_eraseOverlapIntervals_partial_solve_wit_1_pure : eraseOverlapIntervals_partial_solve_wit_1_pure.
Axiom proof_of_eraseOverlapIntervals_partial_solve_wit_1 : eraseOverlapIntervals_partial_solve_wit_1.
Axiom proof_of_eraseOverlapIntervals_partial_solve_wit_2 : eraseOverlapIntervals_partial_solve_wit_2.
Axiom proof_of_eraseOverlapIntervals_partial_solve_wit_3 : eraseOverlapIntervals_partial_solve_wit_3.
Axiom proof_of_eraseOverlapIntervals_partial_solve_wit_4 : eraseOverlapIntervals_partial_solve_wit_4.

End VC_Correct.
