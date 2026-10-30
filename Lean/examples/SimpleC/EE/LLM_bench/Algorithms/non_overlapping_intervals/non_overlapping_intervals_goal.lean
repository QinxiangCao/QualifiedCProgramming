import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_lib
open SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance non_overlapping_intervals_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def swap_intervals_return_wit_1 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full ed_pre n (replace_Znth (j_pre) ((Znth i_pre ed_l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre ed_l (0 : Int))) (ed_l)))))
  ** (intArray.full st_pre n (replace_Znth (j_pre) ((Znth i_pre st_l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))))
|--
  EX st1 : (List Int), EX ed1 : (List Int), EX ps1 : (List interval),
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalSwappedAt ps ps1 i_pre j_pre) ”
  &&  (intArray.full st_pre n st1)
  ** (intArray.full ed_pre n ed1)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ (PairIntervals (replace_Znth (j_pre) ((Znth i_pre st_l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))) (replace_Znth (j_pre) ((Znth i_pre ed_l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre ed_l (0 : Int))) (ed_l)))) ps1) ” &&
  “ (IntervalSwappedAt ps ps1 i_pre j_pre) ”
  &&  emp
)

noncomputable def swap_intervals_partial_solve_wit_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre n st_l)
  ** (intArray.full ed_pre n ed_l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((st_pre + (i_pre * sizeof(INT)))) # Int |-> ((Znth i_pre st_l (0 : Int))))
  ** (intArray.missing_i st_pre i_pre (0 : Int) n st_l)
  ** (intArray.full ed_pre n ed_l)

noncomputable def swap_intervals_partial_solve_wit_2 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre n st_l)
  ** (intArray.full ed_pre n ed_l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((ed_pre + (i_pre * sizeof(INT)))) # Int |-> ((Znth i_pre ed_l (0 : Int))))
  ** (intArray.missing_i ed_pre i_pre (0 : Int) n ed_l)
  ** (intArray.full st_pre n st_l)

noncomputable def swap_intervals_partial_solve_wit_3 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full ed_pre n ed_l)
  ** (intArray.full st_pre n st_l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((st_pre + (j_pre * sizeof(INT)))) # Int |-> ((Znth j_pre st_l (0 : Int))))
  ** (intArray.missing_i st_pre j_pre (0 : Int) n st_l)
  ** (intArray.full ed_pre n ed_l)

noncomputable def swap_intervals_partial_solve_wit_4 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre n st_l)
  ** (intArray.full ed_pre n ed_l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((st_pre + (i_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre i_pre (0 : Int) n st_l)
  ** (intArray.full ed_pre n ed_l)

noncomputable def swap_intervals_partial_solve_wit_5 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))
  ** (intArray.full ed_pre n ed_l)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((ed_pre + (j_pre * sizeof(INT)))) # Int |-> ((Znth j_pre ed_l (0 : Int))))
  ** (intArray.missing_i ed_pre j_pre (0 : Int) n ed_l)
  ** (intArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))

noncomputable def swap_intervals_partial_solve_wit_6 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full ed_pre n ed_l)
  ** (intArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((ed_pre + (i_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ed_pre i_pre (0 : Int) n ed_l)
  ** (intArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))

noncomputable def swap_intervals_partial_solve_wit_7 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full ed_pre n (replace_Znth (i_pre) ((Znth j_pre ed_l (0 : Int))) (ed_l)))
  ** (intArray.full st_pre n (replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((st_pre + (j_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i st_pre j_pre (0 : Int) n (replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))
  ** (intArray.full ed_pre n (replace_Znth (i_pre) ((Znth j_pre ed_l (0 : Int))) (ed_l)))

noncomputable def swap_intervals_partial_solve_wit_8 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (n : Int) (st_pre : Int) (ed_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n)) (PreH5 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre n (replace_Znth (j_pre) ((Znth i_pre st_l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))))
  ** (intArray.full ed_pre n (replace_Znth (i_pre) ((Znth j_pre ed_l (0 : Int))) (ed_l)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((ed_pre + (j_pre * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ed_pre j_pre (0 : Int) n (replace_Znth (i_pre) ((Znth j_pre ed_l (0 : Int))) (ed_l)))
  ** (intArray.full st_pre n (replace_Znth (j_pre) ((Znth i_pre st_l (0 : Int))) ((replace_Znth (i_pre) ((Znth j_pre st_l (0 : Int))) (st_l)))))

noncomputable def partition_intervals_safety_wit_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
  ** ((( &( "pivot_end" ) )) # Int |-> ((Znth high_pre ed_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
|--
  “ ((low_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (low_pre - 1)) ”

noncomputable def partition_intervals_safety_wit_2 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
  ** ((( &( "pivot_end" ) )) # Int |-> ((Znth high_pre ed_l (0 : Int))))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_intervals_safety_wit_3 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : ((Znth j ed1 (0 : Int)) <= pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH10 : (PairIntervals st1 ed1 ps1)) (PreH11 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
  ** (intArray.full st_pre intervalsSize_pre st1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_intervals_safety_wit_4 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalSwappedAt ps1 ps1_2 (i + 1) j)) (PreH3 : ((Znth j ed1 (0 : Int)) <= pivot_end)) (PreH4 : (j < high_pre)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < intervalsSize_pre)) (PreH8 : ((low_pre - 1) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH12 : (PairIntervals st1 ed1 ps1)) (PreH13 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full st_pre intervalsSize_pre st1_2)
  ** (intArray.full ed_pre intervalsSize_pre ed1_2)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def partition_intervals_safety_wit_5 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : ((Znth j ed1 (0 : Int)) > pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH10 : (PairIntervals st1 ed1 ps1)) (PreH11 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
  ** (intArray.full st_pre intervalsSize_pre st1)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def partition_intervals_safety_wit_6 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH9 : (PairIntervals st1 ed1 ps1)) (PreH10 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
  ** (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_intervals_safety_wit_7 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH9 : (PairIntervals st1 ed1 ps1)) (PreH10 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
  ** (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_intervals_safety_wit_8 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalSwappedAt ps1 ps1_2 (i + 1) high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < intervalsSize_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH11 : (PairIntervals st1 ed1 ps1)) (PreH12 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full st_pre intervalsSize_pre st1_2)
  ** (intArray.full ed_pre intervalsSize_pre ed1_2)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_intervals_safety_wit_9 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalSwappedAt ps1 ps1_2 (i + 1) high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < intervalsSize_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH11 : (PairIntervals st1 ed1 ps1)) (PreH12 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full st_pre intervalsSize_pre st1_2)
  ** (intArray.full ed_pre intervalsSize_pre ed1_2)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_intervals_entail_wit_1 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full ed_pre intervalsSize_pre ed_l)
  ** (intArray.full st_pre intervalsSize_pre st_l)
|--
  EX st1 : (List Int), EX ps1 : (List interval), EX ed1 : (List Int),
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ ((Znth high_pre ed_l (0 : Int)) = (Znth high_pre ed1 (0 : Int))) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre (low_pre - 1) low_pre (Znth high_pre ed_l (0 : Int))) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps)) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (PairIntervals st_l ed_l ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre (low_pre - 1) low_pre (Znth high_pre ed_l (0 : Int))) ”
  &&  emp
)

noncomputable def partition_intervals_entail_wit_2_1 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (st1_3 : (List Int)) (ed1_3 : (List Int)) (ps1_3 : (List interval)) (PreH1 : (PairIntervals st1_3 ed1_3 ps1_3)) (PreH2 : (IntervalSwappedAt ps1_2 ps1_3 (i + 1) j)) (PreH3 : ((Znth j ed1_2 (0 : Int)) <= pivot_end)) (PreH4 : (j < high_pre)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < intervalsSize_pre)) (PreH8 : ((low_pre - 1) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (pivot_end = (Znth high_pre ed1_2 (0 : Int)))) (PreH12 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH13 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end)) ,
  (intArray.full st_pre intervalsSize_pre st1_3)
  ** (intArray.full ed_pre intervalsSize_pre ed1_3)
|--
  EX st1 : (List Int), EX ps1 : (List interval), EX ed1 : (List Int),
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ ((low_pre - 1) <= (i + 1)) ” &&
  “ ((i + 1) < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ (pivot_end = (Znth high_pre ed1 (0 : Int))) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre (i + 1) (j + 1) pivot_end) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (st1_3 : (List Int)) (ed1_3 : (List Int)) (ps1_3 : (List interval)) (PreH1 : (PairIntervals st1_3 ed1_3 ps1_3)) (PreH2 : (IntervalSwappedAt ps1_2 ps1_3 (i + 1) j)) (PreH3 : ((Znth j ed1_2 (0 : Int)) <= pivot_end)) (PreH4 : (j < high_pre)) (PreH5 : ((0 : Int) <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < intervalsSize_pre)) (PreH8 : ((low_pre - 1) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (pivot_end = (Znth high_pre ed1_2 (0 : Int)))) (PreH12 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH13 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end)) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ ((low_pre - 1) <= (i + 1)) ” &&
  “ ((i + 1) < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ ((Znth high_pre ed1_2 (0 : Int)) = (Znth high_pre ed1_3 (0 : Int))) ” &&
  “ (PairIntervals st1_3 ed1_3 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre (i + 1) (j + 1) (Znth high_pre ed1_2 (0 : Int))) ”
  &&  emp
)

noncomputable def partition_intervals_entail_wit_2_2 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : ((Znth j ed1_2 (0 : Int)) > pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (pivot_end = (Znth high_pre ed1_2 (0 : Int)))) (PreH10 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH11 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end)) ,
  (intArray.full ed_pre intervalsSize_pre ed1_2)
  ** (intArray.full st_pre intervalsSize_pre st1_2)
|--
  EX st1 : (List Int), EX ps1 : (List interval), EX ed1 : (List Int),
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ (pivot_end = (Znth high_pre ed1 (0 : Int))) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre i (j + 1) pivot_end) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : ((Znth j ed1_2 (0 : Int)) > pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (pivot_end = (Znth high_pre ed1_2 (0 : Int)))) (PreH10 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH11 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end)) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ (i < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ (PairIntervals st1_2 ed1_2 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre i (j + 1) (Znth high_pre ed1_2 (0 : Int))) ”
  &&  emp
)

noncomputable def partition_intervals_return_wit_1 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (st1_3 : (List Int)) (ed1_3 : (List Int)) (ps1_3 : (List interval)) (PreH1 : (PairIntervals st1_3 ed1_3 ps1_3)) (PreH2 : (IntervalSwappedAt ps1_2 ps1_3 (i + 1) high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < intervalsSize_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1_2 (0 : Int)))) (PreH11 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH12 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end)) ,
  (intArray.full st_pre intervalsSize_pre st1_3)
  ** (intArray.full ed_pre intervalsSize_pre ed1_3)
|--
  EX st1 : (List Int), EX ed1 : (List Int), EX ps1 : (List interval),
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 low_pre high_pre) ” &&
  “ (IntervalPartitionedAt ps1 low_pre high_pre (i + 1)) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (st1_3 : (List Int)) (ed1_3 : (List Int)) (ps1_3 : (List interval)) (PreH1 : (PairIntervals st1_3 ed1_3 ps1_3)) (PreH2 : (IntervalSwappedAt ps1_2 ps1_3 (i + 1) high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < intervalsSize_pre)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (pivot_end = (Znth high_pre ed1_2 (0 : Int)))) (PreH11 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH12 : (LomutoScanState ps ps1_2 low_pre high_pre i j pivot_end)) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ (PairIntervals st1_3 ed1_3 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 low_pre high_pre) ” &&
  “ (IntervalPartitionedAt ps1 low_pre high_pre (i + 1)) ”
  &&  emp
)

noncomputable def partition_intervals_partial_solve_wit_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < intervalsSize_pre)) (PreH4 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (((ed_pre + (high_pre * sizeof(INT)))) # Int |-> ((Znth high_pre ed_l (0 : Int))))
  ** (intArray.missing_i ed_pre high_pre (0 : Int) intervalsSize_pre ed_l)
  ** (intArray.full st_pre intervalsSize_pre st_l)

noncomputable def partition_intervals_partial_solve_wit_2 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH9 : (PairIntervals st1 ed1 ps1)) (PreH10 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  “ (j < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (pivot_end = (Znth high_pre ed1 (0 : Int))) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end) ”
  &&  (((ed_pre + (j * sizeof(INT)))) # Int |-> ((Znth j ed1 (0 : Int))))
  ** (intArray.missing_i ed_pre j (0 : Int) intervalsSize_pre ed1)
  ** (intArray.full st_pre intervalsSize_pre st1)

noncomputable def partition_intervals_partial_solve_wit_3_pure : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : ((Znth j ed1 (0 : Int)) <= pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH10 : (PairIntervals st1 ed1 ps1)) (PreH11 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
  ** (intArray.full st_pre intervalsSize_pre st1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < intervalsSize_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < intervalsSize_pre) ” &&
  “ (PairIntervals st1 ed1 ps1) ”

noncomputable def partition_intervals_partial_solve_wit_3_aux : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : ((Znth j ed1 (0 : Int)) <= pivot_end)) (PreH2 : (j < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < intervalsSize_pre)) (PreH6 : ((low_pre - 1) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH10 : (PairIntervals st1 ed1 ps1)) (PreH11 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full ed_pre intervalsSize_pre ed1)
  ** (intArray.full st_pre intervalsSize_pre st1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < intervalsSize_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < intervalsSize_pre) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ ((Znth j ed1 (0 : Int)) <= pivot_end) ” &&
  “ (j < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (pivot_end = (Znth high_pre ed1 (0 : Int))) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)

noncomputable def partition_intervals_partial_solve_wit_3 : Prop := partition_intervals_partial_solve_wit_3_pure -> partition_intervals_partial_solve_wit_3_aux

noncomputable def partition_intervals_partial_solve_wit_4_pure : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH9 : (PairIntervals st1 ed1 ps1)) (PreH10 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_end" ) )) # Int |-> (pivot_end))
  ** (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < intervalsSize_pre) ” &&
  “ ((0 : Int) <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ (PairIntervals st1 ed1 ps1) ”

noncomputable def partition_intervals_partial_solve_wit_4_aux : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (low_pre : Int) (high_pre : Int) (pivot_end : Int) (j : Int) (i : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < intervalsSize_pre)) (PreH5 : ((low_pre - 1) <= i)) (PreH6 : (i < j)) (PreH7 : (j <= high_pre)) (PreH8 : (pivot_end = (Znth high_pre ed1 (0 : Int)))) (PreH9 : (PairIntervals st1 ed1 ps1)) (PreH10 : (LomutoScanState ps ps1 low_pre high_pre i j pivot_end)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < intervalsSize_pre) ” &&
  “ ((0 : Int) <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (j >= high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < intervalsSize_pre) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ (pivot_end = (Znth high_pre ed1 (0 : Int))) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (LomutoScanState ps ps1 low_pre high_pre i j pivot_end) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)

noncomputable def partition_intervals_partial_solve_wit_4 : Prop := partition_intervals_partial_solve_wit_4_pure -> partition_intervals_partial_solve_wit_4_aux

noncomputable def quicksort_intervals_range_safety_wit_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (retval > left_pre)) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH5 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH6 : (left_pre < right_pre)) (PreH7 : ((0 : Int) <= intervalsSize_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : ((-1) <= right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "pivot" ) )) # Int |-> (retval))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((retval - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval - 1)) ”

noncomputable def quicksort_intervals_range_safety_wit_2 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (retval > left_pre)) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH5 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH6 : (left_pre < right_pre)) (PreH7 : ((0 : Int) <= intervalsSize_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : ((-1) <= right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "pivot" ) )) # Int |-> (retval))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_intervals_range_safety_wit_3 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (PreH1 : (pivot < right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps)) (PreH9 : (IntervalPermutation ps current_ps)) (PreH10 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH11 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH12 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)
|--
  “ ((pivot + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pivot + 1)) ”

noncomputable def quicksort_intervals_range_safety_wit_4 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (PreH1 : (pivot < right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps)) (PreH9 : (IntervalPermutation ps current_ps)) (PreH10 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH11 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH12 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_intervals_range_entail_wit_1_1 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalPermutation ps1 ps1_2)) (PreH3 : (IntervalSameOutsideRange ps1 ps1_2 left_pre (retval - 1))) (PreH4 : (IntervalsEndSortedRange ps1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (PairIntervals st1 ed1 ps1)) (PreH7 : (IntervalPermutation ps ps1)) (PreH8 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH9 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH10 : (left_pre < right_pre)) (PreH11 : ((0 : Int) <= intervalsSize_pre)) (PreH12 : ((0 : Int) <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < intervalsSize_pre)) (PreH15 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1_2)
  ** (intArray.full ed_pre intervalsSize_pre ed1_2)
|--
  EX current_st : (List Int), EX current_ed : (List Int), EX current_ps : (List interval),
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (PairIntervals current_st current_ed current_ps) ” &&
  “ (IntervalPermutation ps current_ps) ” &&
  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre) ” &&
  “ (IntervalPartitionedAt current_ps left_pre right_pre retval) ” &&
  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1)) ”
  &&  (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalPermutation ps1 ps1_2)) (PreH3 : (IntervalSameOutsideRange ps1 ps1_2 left_pre (retval - 1))) (PreH4 : (IntervalsEndSortedRange ps1_2 left_pre (retval - 1))) (PreH5 : (retval > left_pre)) (PreH6 : (PairIntervals st1 ed1 ps1)) (PreH7 : (IntervalPermutation ps ps1)) (PreH8 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH9 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH10 : (left_pre < right_pre)) (PreH11 : ((0 : Int) <= intervalsSize_pre)) (PreH12 : ((0 : Int) <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < intervalsSize_pre)) (PreH15 : (PairIntervals st_l ed_l ps)) ,
  TT && emp 
|--
  EX current_ps : (List interval),
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (PairIntervals st1_2 ed1_2 current_ps) ” &&
  “ (IntervalPermutation ps current_ps) ” &&
  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre) ” &&
  “ (IntervalPartitionedAt current_ps left_pre right_pre retval) ” &&
  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1)) ”
  &&  emp
)

noncomputable def quicksort_intervals_range_entail_wit_1_2 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (retval <= left_pre)) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH5 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH6 : (left_pre < right_pre)) (PreH7 : ((0 : Int) <= intervalsSize_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : ((-1) <= right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  EX current_st : (List Int), EX current_ed : (List Int), EX current_ps : (List interval),
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (PairIntervals current_st current_ed current_ps) ” &&
  “ (IntervalPermutation ps current_ps) ” &&
  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre) ” &&
  “ (IntervalPartitionedAt current_ps left_pre right_pre retval) ” &&
  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1)) ”
  &&  (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (retval <= left_pre)) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH5 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH6 : (left_pre < right_pre)) (PreH7 : ((0 : Int) <= intervalsSize_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : ((-1) <= right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (PairIntervals st_l ed_l ps)) ,
  TT && emp 
|--
  EX current_ps : (List interval),
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (PairIntervals st1 ed1 current_ps) ” &&
  “ (IntervalPermutation ps current_ps) ” &&
  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre) ” &&
  “ (IntervalPartitionedAt current_ps left_pre right_pre retval) ” &&
  “ (IntervalsEndSortedRange current_ps left_pre (retval - 1)) ”
  &&  emp
)

noncomputable def quicksort_intervals_range_return_wit_1 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalPermutation current_ps ps1_2)) (PreH3 : (IntervalSameOutsideRange current_ps ps1_2 (pivot + 1) right_pre)) (PreH4 : (IntervalsEndSortedRange ps1_2 (pivot + 1) right_pre)) (PreH5 : (pivot < right_pre)) (PreH6 : ((0 : Int) <= intervalsSize_pre)) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre < right_pre)) (PreH9 : (right_pre < intervalsSize_pre)) (PreH10 : (left_pre <= pivot)) (PreH11 : (pivot <= right_pre)) (PreH12 : (PairIntervals current_st current_ed current_ps)) (PreH13 : (IntervalPermutation ps current_ps)) (PreH14 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH15 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH16 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  (intArray.full st_pre intervalsSize_pre st1_2)
  ** (intArray.full ed_pre intervalsSize_pre ed1_2)
|--
  EX st1 : (List Int), EX ed1 : (List Int), EX ps1 : (List interval),
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre) ” &&
  “ (IntervalsEndSortedRange ps1 left_pre right_pre) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalPermutation current_ps ps1_2)) (PreH3 : (IntervalSameOutsideRange current_ps ps1_2 (pivot + 1) right_pre)) (PreH4 : (IntervalsEndSortedRange ps1_2 (pivot + 1) right_pre)) (PreH5 : (pivot < right_pre)) (PreH6 : ((0 : Int) <= intervalsSize_pre)) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre < right_pre)) (PreH9 : (right_pre < intervalsSize_pre)) (PreH10 : (left_pre <= pivot)) (PreH11 : (pivot <= right_pre)) (PreH12 : (PairIntervals current_st current_ed current_ps)) (PreH13 : (IntervalPermutation ps current_ps)) (PreH14 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH15 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH16 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ (PairIntervals st1_2 ed1_2 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre) ” &&
  “ (IntervalsEndSortedRange ps1 left_pre right_pre) ”
  &&  emp
)

noncomputable def quicksort_intervals_range_return_wit_2 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (PreH1 : (pivot >= right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps)) (PreH9 : (IntervalPermutation ps current_ps)) (PreH10 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH11 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH12 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)
|--
  EX st1 : (List Int), EX ed1 : (List Int), EX ps1 : (List interval),
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre) ” &&
  “ (IntervalsEndSortedRange ps1 left_pre right_pre) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (PreH1 : (pivot >= right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps)) (PreH9 : (IntervalPermutation ps current_ps)) (PreH10 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH11 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH12 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ (PairIntervals current_st current_ed ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre) ” &&
  “ (IntervalsEndSortedRange ps1 left_pre right_pre) ”
  &&  emp
)

noncomputable def quicksort_intervals_range_return_wit_3 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  EX st1 : (List Int), EX ed1 : (List Int), EX ps1 : (List interval),
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre) ” &&
  “ (IntervalsEndSortedRange ps1 left_pre right_pre) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps)) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ (PairIntervals st_l ed_l ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre) ” &&
  “ (IntervalsEndSortedRange ps1 left_pre right_pre) ”
  &&  emp
)

noncomputable def quicksort_intervals_range_partial_solve_wit_1_pure : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps)) ,
  ((( &( "pivot" ) )) # Int |->_)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ”

noncomputable def quicksort_intervals_range_partial_solve_wit_1_aux : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ” &&
  “ (left_pre < right_pre) ” &&
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)

noncomputable def quicksort_intervals_range_partial_solve_wit_1 : Prop := quicksort_intervals_range_partial_solve_wit_1_pure -> quicksort_intervals_range_partial_solve_wit_1_aux

noncomputable def quicksort_intervals_range_partial_solve_wit_2_pure : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (retval > left_pre)) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH5 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH6 : (left_pre < right_pre)) (PreH7 : ((0 : Int) <= intervalsSize_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : ((-1) <= right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "pivot" ) )) # Int |-> (retval))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= (retval - 1)) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ ((retval - 1) < intervalsSize_pre) ”
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (intervalsSize_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (intervalsSize_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (PairIntervals st1 ed1 ps1)) (PreH11 : (IntervalPermutation ps ps1)) (PreH12 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH13 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= intervalsSize_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < intervalsSize_pre)) (PreH19 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "pivot" ) )) # Int |-> (retval))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((retval - 1) < intervalsSize_pre) ”
)

noncomputable def quicksort_intervals_range_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (intervalsSize_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (intervalsSize_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (PairIntervals st1 ed1 ps1)) (PreH11 : (IntervalPermutation ps ps1)) (PreH12 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH13 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH14 : (left_pre < right_pre)) (PreH15 : ((0 : Int) <= intervalsSize_pre)) (PreH16 : ((0 : Int) <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < intervalsSize_pre)) (PreH19 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "pivot" ) )) # Int |-> (retval))
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
|--
  “ ((retval - 1) < intervalsSize_pre) ”

noncomputable def quicksort_intervals_range_partial_solve_wit_2_aux : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (retval : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (retval > left_pre)) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalSameOutsideRange ps ps1 left_pre right_pre)) (PreH5 : (IntervalPartitionedAt ps1 left_pre right_pre retval)) (PreH6 : (left_pre < right_pre)) (PreH7 : ((0 : Int) <= intervalsSize_pre)) (PreH8 : ((0 : Int) <= left_pre)) (PreH9 : ((-1) <= right_pre)) (PreH10 : (right_pre < intervalsSize_pre)) (PreH11 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= (retval - 1)) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ ((retval - 1) < intervalsSize_pre) ” &&
  “ (retval > left_pre) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalSameOutsideRange ps ps1 left_pre right_pre) ” &&
  “ (IntervalPartitionedAt ps1 left_pre right_pre retval) ” &&
  “ (left_pre < right_pre) ” &&
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)

noncomputable def quicksort_intervals_range_partial_solve_wit_2 : Prop := quicksort_intervals_range_partial_solve_wit_2_pure -> quicksort_intervals_range_partial_solve_wit_2_aux

noncomputable def quicksort_intervals_range_partial_solve_wit_3_pure : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (PreH1 : (pivot < right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps)) (PreH9 : (IntervalPermutation ps current_ps)) (PreH10 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH11 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH12 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "pivot" ) )) # Int |-> (pivot))
  ** (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (PairIntervals current_st current_ed current_ps) ”

noncomputable def quicksort_intervals_range_partial_solve_wit_3_aux : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (left_pre : Int) (right_pre : Int) (pivot : Int) (current_st : (List Int)) (current_ed : (List Int)) (current_ps : (List interval)) (PreH1 : (pivot < right_pre)) (PreH2 : ((0 : Int) <= intervalsSize_pre)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < intervalsSize_pre)) (PreH6 : (left_pre <= pivot)) (PreH7 : (pivot <= right_pre)) (PreH8 : (PairIntervals current_st current_ed current_ps)) (PreH9 : (IntervalPermutation ps current_ps)) (PreH10 : (IntervalSameOutsideRange ps current_ps left_pre right_pre)) (PreH11 : (IntervalPartitionedAt current_ps left_pre right_pre pivot)) (PreH12 : (IntervalsEndSortedRange current_ps left_pre (pivot - 1))) ,
  (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= (pivot + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (PairIntervals current_st current_ed current_ps) ” &&
  “ (pivot < right_pre) ” &&
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < intervalsSize_pre) ” &&
  “ (left_pre <= pivot) ” &&
  “ (pivot <= right_pre) ” &&
  “ (PairIntervals current_st current_ed current_ps) ” &&
  “ (IntervalPermutation ps current_ps) ” &&
  “ (IntervalSameOutsideRange ps current_ps left_pre right_pre) ” &&
  “ (IntervalPartitionedAt current_ps left_pre right_pre pivot) ” &&
  “ (IntervalsEndSortedRange current_ps left_pre (pivot - 1)) ”
  &&  (intArray.full st_pre intervalsSize_pre current_st)
  ** (intArray.full ed_pre intervalsSize_pre current_ed)

noncomputable def quicksort_intervals_range_partial_solve_wit_3 : Prop := quicksort_intervals_range_partial_solve_wit_3_pure -> quicksort_intervals_range_partial_solve_wit_3_aux

noncomputable def quicksort_intervals_safety_wit_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (PreH1 : ((0 : Int) <= intervalsSize_pre)) (PreH2 : (PairIntervals st_l ed_l ps)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((intervalsSize_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (intervalsSize_pre - 1)) ”

noncomputable def quicksort_intervals_safety_wit_2 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (PreH1 : ((0 : Int) <= intervalsSize_pre)) (PreH2 : (PairIntervals st_l ed_l ps)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def quicksort_intervals_safety_wit_3 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (PreH1 : ((0 : Int) <= intervalsSize_pre)) (PreH2 : (PairIntervals st_l ed_l ps)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_intervals_return_wit_1 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalPermutation ps ps1_2)) (PreH3 : (IntervalSameOutsideRange ps ps1_2 (0 : Int) (intervalsSize_pre - 1))) (PreH4 : (IntervalsEndSortedRange ps1_2 (0 : Int) (intervalsSize_pre - 1))) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st1_2)
  ** (intArray.full ed_pre intervalsSize_pre ed1_2)
|--
  EX st1 : (List Int), EX ed1 : (List Int), EX ps1 : (List interval),
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalsEndSorted ps1) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1_2 : (List interval)) (PreH1 : (PairIntervals st1_2 ed1_2 ps1_2)) (PreH2 : (IntervalPermutation ps ps1_2)) (PreH3 : (IntervalSameOutsideRange ps ps1_2 (0 : Int) (intervalsSize_pre - 1))) (PreH4 : (IntervalsEndSortedRange ps1_2 (0 : Int) (intervalsSize_pre - 1))) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (PairIntervals st_l ed_l ps)) ,
  TT && emp 
|--
  EX ps1 : (List interval),
  “ (PairIntervals st1_2 ed1_2 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalsEndSorted ps1) ”
  &&  emp
)

noncomputable def quicksort_intervals_partial_solve_wit_1_pure : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (PreH1 : ((0 : Int) <= intervalsSize_pre)) (PreH2 : (PairIntervals st_l ed_l ps)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (intervalsSize_pre - 1)) ” &&
  “ ((intervalsSize_pre - 1) < intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ”

noncomputable def quicksort_intervals_partial_solve_wit_1_aux : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (PreH1 : ((0 : Int) <= intervalsSize_pre)) (PreH2 : (PairIntervals st_l ed_l ps)) ,
  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (intervalsSize_pre - 1)) ” &&
  “ ((intervalsSize_pre - 1) < intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ” &&
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ”
  &&  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)

noncomputable def quicksort_intervals_partial_solve_wit_1 : Prop := quicksort_intervals_partial_solve_wit_1_pure -> quicksort_intervals_partial_solve_wit_1_aux

noncomputable def eraseOverlapIntervals_safety_wit_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (PairIntervals st1 ed1 ps1)) (PreH2 : (IntervalPermutation ps ps1)) (PreH3 : (IntervalsEndSorted ps1)) (PreH4 : ((0 : Int) <= intervalsSize_pre)) (PreH5 : (intervalsSize_pre <= 1000)) (PreH6 : (PairIntervals st_l ed_l ps)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH8 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def eraseOverlapIntervals_safety_wit_2 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre = (0 : Int))) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def eraseOverlapIntervals_safety_wit_3 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre ≠ (0 : Int))) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  ((( &( "kept" ) )) # Int |->_)
  ** (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def eraseOverlapIntervals_safety_wit_4 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre ≠ (0 : Int))) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  ((( &( "last_end" ) )) # Int |->_)
  ** ((( &( "kept" ) )) # Int |-> (1))
  ** (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def eraseOverlapIntervals_safety_wit_5 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre ≠ (0 : Int))) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
  ** ((( &( "last_end" ) )) # Int |-> ((Znth (0 : Int) ed1 (0 : Int))))
  ** ((( &( "kept" ) )) # Int |-> (1))
  ** (intArray.full st_pre intervalsSize_pre st1)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def eraseOverlapIntervals_safety_wit_6 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st (0 : Int)) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH11 : (IntervalPermutation ps sorted_ps)) (PreH12 : (IntervalsEndSorted sorted_ps)) (PreH13 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "last_end" ) )) # Int |-> (last_end))
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
|--
  “ ((kept + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (kept + 1)) ”

noncomputable def eraseOverlapIntervals_safety_wit_7 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st (0 : Int)) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH11 : (IntervalPermutation ps sorted_ps)) (PreH12 : (IntervalsEndSorted sorted_ps)) (PreH13 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  (intArray.full ed_pre intervalsSize_pre sorted_ed)
  ** (intArray.full st_pre intervalsSize_pre sorted_st)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> ((kept + 1)))
  ** ((( &( "last_end" ) )) # Int |-> ((Znth i sorted_ed (0 : Int))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def eraseOverlapIntervals_safety_wit_8 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st (0 : Int)) < last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH11 : (IntervalPermutation ps sorted_ps)) (PreH12 : (IntervalsEndSorted sorted_ps)) (PreH13 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "last_end" ) )) # Int |-> (last_end))
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def eraseOverlapIntervals_safety_wit_9 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : (i >= intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH8 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH10 : (IntervalPermutation ps sorted_ps)) (PreH11 : (IntervalsEndSorted sorted_ps)) (PreH12 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** ((( &( "kept" ) )) # Int |-> (kept))
  ** ((( &( "last_end" ) )) # Int |-> (last_end))
  ** (intArray.full st_pre intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
|--
  “ ((intervalsSize_pre - kept) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (intervalsSize_pre - kept)) ”

noncomputable def eraseOverlapIntervals_entail_wit_1 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre ≠ (0 : Int))) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  (intArray.full ed_pre intervalsSize_pre ed1)
  ** (intArray.full st_pre intervalsSize_pre st1)
|--
  EX sorted_st : (List Int), EX sorted_ed : (List Int), EX sorted_ps : (List interval),
  “ (1 <= 1) ” &&
  “ (1 <= intervalsSize_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 1) ” &&
  “ (PairIntervals sorted_st sorted_ed sorted_ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) sorted_st) ” &&
  “ (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) sorted_ed) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps 1 1 (Znth (0 : Int) ed1 (0 : Int))) ”
  &&  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre ≠ (0 : Int))) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  TT && emp 
|--
  EX sorted_ps : (List interval),
  “ (1 <= 1) ” &&
  “ (1 <= intervalsSize_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= 1) ” &&
  “ (PairIntervals st1 ed1 sorted_ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) st1) ” &&
  “ (Forall2 (LT.lt (α := Int)) st1 ed1) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) ed1) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps 1 1 (Znth (0 : Int) ed1 (0 : Int))) ”
  &&  emp
)

noncomputable def eraseOverlapIntervals_entail_wit_2_1 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st_2 : (List Int)) (sorted_ed_2 : (List Int)) (sorted_ps_2 : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st_2 (0 : Int)) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st_2)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st_2 sorted_ed_2)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed_2)) (PreH11 : (IntervalPermutation ps sorted_ps_2)) (PreH12 : (IntervalsEndSorted sorted_ps_2)) (PreH13 : (GreedyPrefixState sorted_ps_2 i kept last_end)) ,
  (intArray.full ed_pre intervalsSize_pre sorted_ed_2)
  ** (intArray.full st_pre intervalsSize_pre sorted_st_2)
|--
  EX sorted_st : (List Int), EX sorted_ed : (List Int), EX sorted_ps : (List interval),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= intervalsSize_pre) ” &&
  “ (1 <= (kept + 1)) ” &&
  “ ((kept + 1) <= (i + 1)) ” &&
  “ (PairIntervals sorted_st sorted_ed sorted_ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) sorted_st) ” &&
  “ (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) sorted_ed) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps (i + 1) (kept + 1) (Znth i sorted_ed_2 (0 : Int))) ”
  &&  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (last_end : Int) (sorted_st_2 : (List Int)) (sorted_ed_2 : (List Int)) (sorted_ps_2 : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st_2 (0 : Int)) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st_2)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st_2 sorted_ed_2)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed_2)) (PreH11 : (IntervalPermutation ps sorted_ps_2)) (PreH12 : (IntervalsEndSorted sorted_ps_2)) (PreH13 : (GreedyPrefixState sorted_ps_2 i kept last_end)) ,
  TT && emp 
|--
  EX sorted_ps : (List interval),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= intervalsSize_pre) ” &&
  “ (1 <= (kept + 1)) ” &&
  “ ((kept + 1) <= (i + 1)) ” &&
  “ (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps (i + 1) (kept + 1) (Znth i sorted_ed_2 (0 : Int))) ”
  &&  emp
)

noncomputable def eraseOverlapIntervals_entail_wit_2_2 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st_2 : (List Int)) (sorted_ed_2 : (List Int)) (sorted_ps_2 : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st_2 (0 : Int)) < last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st_2)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st_2 sorted_ed_2)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed_2)) (PreH11 : (IntervalPermutation ps sorted_ps_2)) (PreH12 : (IntervalsEndSorted sorted_ps_2)) (PreH13 : (GreedyPrefixState sorted_ps_2 i kept last_end)) ,
  (intArray.full st_pre intervalsSize_pre sorted_st_2)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed_2)
|--
  EX sorted_st : (List Int), EX sorted_ed : (List Int), EX sorted_ps : (List interval),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= intervalsSize_pre) ” &&
  “ (1 <= kept) ” &&
  “ (kept <= (i + 1)) ” &&
  “ (PairIntervals sorted_st sorted_ed sorted_ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) sorted_st) ” &&
  “ (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) sorted_ed) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps (i + 1) kept last_end) ”
  &&  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (last_end : Int) (sorted_st_2 : (List Int)) (sorted_ed_2 : (List Int)) (sorted_ps_2 : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st_2 (0 : Int)) < last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps_2)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st_2)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st_2 sorted_ed_2)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed_2)) (PreH11 : (IntervalPermutation ps sorted_ps_2)) (PreH12 : (IntervalsEndSorted sorted_ps_2)) (PreH13 : (GreedyPrefixState sorted_ps_2 i kept last_end)) ,
  TT && emp 
|--
  EX sorted_ps : (List interval),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= intervalsSize_pre) ” &&
  “ (kept <= (i + 1)) ” &&
  “ (PairIntervals sorted_st_2 sorted_ed_2 sorted_ps) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps (i + 1) kept last_end) ”
  &&  emp
)

noncomputable def eraseOverlapIntervals_return_wit_1 : Prop :=
  (
forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : (i >= intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH8 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH10 : (IntervalPermutation ps sorted_ps)) (PreH11 : (IntervalsEndSorted sorted_ps)) (PreH12 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
|--
  EX ed1 : (List Int), EX st1 : (List Int),
  “ (MinimumRemovals ps (intervalsSize_pre - kept)) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : (i >= intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH8 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH10 : (IntervalPermutation ps sorted_ps)) (PreH11 : (IntervalsEndSorted sorted_ps)) (PreH12 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  TT && emp 
|--
  “ (MinimumRemovals ps (intervalsSize_pre - kept)) ”
  &&  emp
)

noncomputable def eraseOverlapIntervals_return_wit_1_split_goal_1 : Prop :=
  forall (ps : (List interval)) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : (i >= intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH8 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH10 : (IntervalPermutation ps sorted_ps)) (PreH11 : (IntervalsEndSorted sorted_ps)) (PreH12 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  (MinimumRemovals ps (intervalsSize_pre - kept))

noncomputable def eraseOverlapIntervals_return_wit_2 : Prop :=
  (
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre = (0 : Int))) (PreH2 : (PairIntervals st1_2 ed1_2 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  (intArray.full st_pre intervalsSize_pre st1_2)
  ** (intArray.full ed_pre intervalsSize_pre ed1_2)
|--
  EX ed1 : (List Int), EX st1 : (List Int),
  “ (MinimumRemovals ps (0 : Int)) ”
  &&  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
) \/
(
forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre = (0 : Int))) (PreH2 : (PairIntervals st1_2 ed1_2 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  TT && emp 
|--
  “ (MinimumRemovals ps (0 : Int)) ”
  &&  emp
)

noncomputable def eraseOverlapIntervals_return_wit_2_split_goal_1 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (intervalsSize_pre : Int) (st1_2 : (List Int)) (ed1_2 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre = (0 : Int))) (PreH2 : (PairIntervals st1_2 ed1_2 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  (MinimumRemovals ps (0 : Int))

noncomputable def eraseOverlapIntervals_partial_solve_wit_1_pure : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (PreH1 : ((0 : Int) <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps)) (PreH4 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH5 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  ((( &( "st" ) )) # Ptr |-> (st_pre))
  ** ((( &( "ed" ) )) # Ptr |-> (ed_pre))
  ** ((( &( "intervalsSize" ) )) # Int |-> (intervalsSize_pre))
  ** (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ”

noncomputable def eraseOverlapIntervals_partial_solve_wit_1_aux : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (PreH1 : ((0 : Int) <= intervalsSize_pre)) (PreH2 : (intervalsSize_pre <= 1000)) (PreH3 : (PairIntervals st_l ed_l ps)) (PreH4 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH5 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)
|--
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ (PairIntervals st_l ed_l ps) ” &&
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ (intervalsSize_pre <= 1000) ” &&
  “ (PairIntervals st_l ed_l ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) st_l) ” &&
  “ (Forall2 (LT.lt (α := Int)) st_l ed_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) ed_l) ”
  &&  (intArray.full st_pre intervalsSize_pre st_l)
  ** (intArray.full ed_pre intervalsSize_pre ed_l)

noncomputable def eraseOverlapIntervals_partial_solve_wit_1 : Prop := eraseOverlapIntervals_partial_solve_wit_1_pure -> eraseOverlapIntervals_partial_solve_wit_1_aux

noncomputable def eraseOverlapIntervals_partial_solve_wit_2 : Prop :=
  forall (ps : (List interval)) (ed_l : (List Int)) (st_l : (List Int)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (st1 : (List Int)) (ed1 : (List Int)) (ps1 : (List interval)) (PreH1 : (intervalsSize_pre ≠ (0 : Int))) (PreH2 : (PairIntervals st1 ed1 ps1)) (PreH3 : (IntervalPermutation ps ps1)) (PreH4 : (IntervalsEndSorted ps1)) (PreH5 : ((0 : Int) <= intervalsSize_pre)) (PreH6 : (intervalsSize_pre <= 1000)) (PreH7 : (PairIntervals st_l ed_l ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) st_l)) (PreH9 : (Forall2 (LT.lt (α := Int)) st_l ed_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) ed_l)) ,
  (intArray.full st_pre intervalsSize_pre st1)
  ** (intArray.full ed_pre intervalsSize_pre ed1)
|--
  “ (intervalsSize_pre ≠ (0 : Int)) ” &&
  “ (PairIntervals st1 ed1 ps1) ” &&
  “ (IntervalPermutation ps ps1) ” &&
  “ (IntervalsEndSorted ps1) ” &&
  “ ((0 : Int) <= intervalsSize_pre) ” &&
  “ (intervalsSize_pre <= 1000) ” &&
  “ (PairIntervals st_l ed_l ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) st_l) ” &&
  “ (Forall2 (LT.lt (α := Int)) st_l ed_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) ed_l) ”
  &&  (((ed_pre + ((0 : Int) * sizeof(INT)))) # Int |-> ((Znth (0 : Int) ed1 (0 : Int))))
  ** (intArray.missing_i ed_pre (0 : Int) (0 : Int) intervalsSize_pre ed1)
  ** (intArray.full st_pre intervalsSize_pre st1)

noncomputable def eraseOverlapIntervals_partial_solve_wit_3 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : (i < intervalsSize_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= intervalsSize_pre)) (PreH4 : (1 <= kept)) (PreH5 : (kept <= i)) (PreH6 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH8 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH10 : (IntervalPermutation ps sorted_ps)) (PreH11 : (IntervalsEndSorted sorted_ps)) (PreH12 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
|--
  “ (i < intervalsSize_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= intervalsSize_pre) ” &&
  “ (1 <= kept) ” &&
  “ (kept <= i) ” &&
  “ (PairIntervals sorted_st sorted_ed sorted_ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) sorted_st) ” &&
  “ (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) sorted_ed) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps i kept last_end) ”
  &&  (((st_pre + (i * sizeof(INT)))) # Int |-> ((Znth i sorted_st (0 : Int))))
  ** (intArray.missing_i st_pre i (0 : Int) intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)

noncomputable def eraseOverlapIntervals_partial_solve_wit_4 : Prop :=
  forall (ps : (List interval)) (st_pre : Int) (ed_pre : Int) (intervalsSize_pre : Int) (last_end : Int) (sorted_st : (List Int)) (sorted_ed : (List Int)) (sorted_ps : (List interval)) (kept : Int) (i : Int) (PreH1 : ((Znth i sorted_st (0 : Int)) >= last_end)) (PreH2 : (i < intervalsSize_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= intervalsSize_pre)) (PreH5 : (1 <= kept)) (PreH6 : (kept <= i)) (PreH7 : (PairIntervals sorted_st sorted_ed sorted_ps)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) sorted_st)) (PreH9 : (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed)) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) sorted_ed)) (PreH11 : (IntervalPermutation ps sorted_ps)) (PreH12 : (IntervalsEndSorted sorted_ps)) (PreH13 : (GreedyPrefixState sorted_ps i kept last_end)) ,
  (intArray.full st_pre intervalsSize_pre sorted_st)
  ** (intArray.full ed_pre intervalsSize_pre sorted_ed)
|--
  “ ((Znth i sorted_st (0 : Int)) >= last_end) ” &&
  “ (i < intervalsSize_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= intervalsSize_pre) ” &&
  “ (1 <= kept) ” &&
  “ (kept <= i) ” &&
  “ (PairIntervals sorted_st sorted_ed sorted_ps) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) sorted_st) ” &&
  “ (Forall2 (LT.lt (α := Int)) sorted_st sorted_ed) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) sorted_ed) ” &&
  “ (IntervalPermutation ps sorted_ps) ” &&
  “ (IntervalsEndSorted sorted_ps) ” &&
  “ (GreedyPrefixState sorted_ps i kept last_end) ”
  &&  (((ed_pre + (i * sizeof(INT)))) # Int |-> ((Znth i sorted_ed (0 : Int))))
  ** (intArray.missing_i ed_pre i (0 : Int) intervalsSize_pre sorted_ed)
  ** (intArray.full st_pre intervalsSize_pre sorted_st)


structure VC_Correct : Type where
  proof_of_swap_intervals_partial_solve_wit_1 : swap_intervals_partial_solve_wit_1
  proof_of_swap_intervals_partial_solve_wit_2 : swap_intervals_partial_solve_wit_2
  proof_of_swap_intervals_partial_solve_wit_3 : swap_intervals_partial_solve_wit_3
  proof_of_swap_intervals_partial_solve_wit_4 : swap_intervals_partial_solve_wit_4
  proof_of_swap_intervals_partial_solve_wit_5 : swap_intervals_partial_solve_wit_5
  proof_of_swap_intervals_partial_solve_wit_6 : swap_intervals_partial_solve_wit_6
  proof_of_swap_intervals_partial_solve_wit_7 : swap_intervals_partial_solve_wit_7
  proof_of_swap_intervals_partial_solve_wit_8 : swap_intervals_partial_solve_wit_8
  proof_of_partition_intervals_safety_wit_1 : partition_intervals_safety_wit_1
  proof_of_partition_intervals_safety_wit_2 : partition_intervals_safety_wit_2
  proof_of_partition_intervals_safety_wit_3 : partition_intervals_safety_wit_3
  proof_of_partition_intervals_safety_wit_4 : partition_intervals_safety_wit_4
  proof_of_partition_intervals_safety_wit_5 : partition_intervals_safety_wit_5
  proof_of_partition_intervals_safety_wit_6 : partition_intervals_safety_wit_6
  proof_of_partition_intervals_safety_wit_7 : partition_intervals_safety_wit_7
  proof_of_partition_intervals_safety_wit_8 : partition_intervals_safety_wit_8
  proof_of_partition_intervals_safety_wit_9 : partition_intervals_safety_wit_9
  proof_of_partition_intervals_partial_solve_wit_1 : partition_intervals_partial_solve_wit_1
  proof_of_partition_intervals_partial_solve_wit_2 : partition_intervals_partial_solve_wit_2
  proof_of_partition_intervals_partial_solve_wit_3_pure : partition_intervals_partial_solve_wit_3_pure
  proof_of_partition_intervals_partial_solve_wit_3 : partition_intervals_partial_solve_wit_3
  proof_of_partition_intervals_partial_solve_wit_4_pure : partition_intervals_partial_solve_wit_4_pure
  proof_of_partition_intervals_partial_solve_wit_4 : partition_intervals_partial_solve_wit_4
  proof_of_quicksort_intervals_range_safety_wit_1 : quicksort_intervals_range_safety_wit_1
  proof_of_quicksort_intervals_range_safety_wit_2 : quicksort_intervals_range_safety_wit_2
  proof_of_quicksort_intervals_range_safety_wit_3 : quicksort_intervals_range_safety_wit_3
  proof_of_quicksort_intervals_range_safety_wit_4 : quicksort_intervals_range_safety_wit_4
  proof_of_quicksort_intervals_range_partial_solve_wit_1_pure : quicksort_intervals_range_partial_solve_wit_1_pure
  proof_of_quicksort_intervals_range_partial_solve_wit_1 : quicksort_intervals_range_partial_solve_wit_1
  proof_of_quicksort_intervals_range_partial_solve_wit_2 : quicksort_intervals_range_partial_solve_wit_2
  proof_of_quicksort_intervals_range_partial_solve_wit_3_pure : quicksort_intervals_range_partial_solve_wit_3_pure
  proof_of_quicksort_intervals_range_partial_solve_wit_3 : quicksort_intervals_range_partial_solve_wit_3
  proof_of_quicksort_intervals_safety_wit_1 : quicksort_intervals_safety_wit_1
  proof_of_quicksort_intervals_safety_wit_2 : quicksort_intervals_safety_wit_2
  proof_of_quicksort_intervals_safety_wit_3 : quicksort_intervals_safety_wit_3
  proof_of_quicksort_intervals_partial_solve_wit_1_pure : quicksort_intervals_partial_solve_wit_1_pure
  proof_of_quicksort_intervals_partial_solve_wit_1 : quicksort_intervals_partial_solve_wit_1
  proof_of_eraseOverlapIntervals_safety_wit_1 : eraseOverlapIntervals_safety_wit_1
  proof_of_eraseOverlapIntervals_safety_wit_2 : eraseOverlapIntervals_safety_wit_2
  proof_of_eraseOverlapIntervals_safety_wit_3 : eraseOverlapIntervals_safety_wit_3
  proof_of_eraseOverlapIntervals_safety_wit_4 : eraseOverlapIntervals_safety_wit_4
  proof_of_eraseOverlapIntervals_safety_wit_5 : eraseOverlapIntervals_safety_wit_5
  proof_of_eraseOverlapIntervals_safety_wit_6 : eraseOverlapIntervals_safety_wit_6
  proof_of_eraseOverlapIntervals_safety_wit_7 : eraseOverlapIntervals_safety_wit_7
  proof_of_eraseOverlapIntervals_safety_wit_8 : eraseOverlapIntervals_safety_wit_8
  proof_of_eraseOverlapIntervals_safety_wit_9 : eraseOverlapIntervals_safety_wit_9
  proof_of_eraseOverlapIntervals_partial_solve_wit_1_pure : eraseOverlapIntervals_partial_solve_wit_1_pure
  proof_of_eraseOverlapIntervals_partial_solve_wit_1 : eraseOverlapIntervals_partial_solve_wit_1
  proof_of_eraseOverlapIntervals_partial_solve_wit_2 : eraseOverlapIntervals_partial_solve_wit_2
  proof_of_eraseOverlapIntervals_partial_solve_wit_3 : eraseOverlapIntervals_partial_solve_wit_3
  proof_of_eraseOverlapIntervals_partial_solve_wit_4 : eraseOverlapIntervals_partial_solve_wit_4
  proof_of_swap_intervals_return_wit_1 : swap_intervals_return_wit_1
  proof_of_partition_intervals_entail_wit_1 : partition_intervals_entail_wit_1
  proof_of_partition_intervals_entail_wit_2_1 : partition_intervals_entail_wit_2_1
  proof_of_partition_intervals_entail_wit_2_2 : partition_intervals_entail_wit_2_2
  proof_of_partition_intervals_return_wit_1 : partition_intervals_return_wit_1
  proof_of_quicksort_intervals_range_entail_wit_1_1 : quicksort_intervals_range_entail_wit_1_1
  proof_of_quicksort_intervals_range_entail_wit_1_2 : quicksort_intervals_range_entail_wit_1_2
  proof_of_quicksort_intervals_range_return_wit_1 : quicksort_intervals_range_return_wit_1
  proof_of_quicksort_intervals_range_return_wit_2 : quicksort_intervals_range_return_wit_2
  proof_of_quicksort_intervals_range_return_wit_3 : quicksort_intervals_range_return_wit_3
  proof_of_quicksort_intervals_range_partial_solve_wit_2_pure : quicksort_intervals_range_partial_solve_wit_2_pure
  proof_of_quicksort_intervals_return_wit_1 : quicksort_intervals_return_wit_1
  proof_of_eraseOverlapIntervals_entail_wit_1 : eraseOverlapIntervals_entail_wit_1
  proof_of_eraseOverlapIntervals_entail_wit_2_1 : eraseOverlapIntervals_entail_wit_2_1
  proof_of_eraseOverlapIntervals_entail_wit_2_2 : eraseOverlapIntervals_entail_wit_2_2
  proof_of_eraseOverlapIntervals_return_wit_1 : eraseOverlapIntervals_return_wit_1
  proof_of_eraseOverlapIntervals_return_wit_2 : eraseOverlapIntervals_return_wit_2

end SimpleC.EE.LLM_bench.Algorithms.non_overlapping_intervals.non_overlapping_intervals_goal
