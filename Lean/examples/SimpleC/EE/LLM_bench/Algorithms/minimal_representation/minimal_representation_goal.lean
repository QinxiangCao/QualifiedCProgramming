import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance minimal_representation_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def minimal_representation_safety_wit_1 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((0 : Int) <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "p" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "b" ) ) 2000)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_2 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.full a_pre n_pre l)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((n_pre + p) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + p)) ”

noncomputable def minimal_representation_safety_wit_3 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg ( &( "b" ) ) n_pre ((n_pre + p) + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) ((n_pre + p) + 1) (2 * n_pre))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((p + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (p + 1)) ”

noncomputable def minimal_representation_safety_wit_4 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) p n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_5 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) p n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def minimal_representation_safety_wit_6 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |-> (1))
  ** ((( &( "i" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (p))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) p n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_7 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ False ”

noncomputable def minimal_representation_safety_wit_8 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (j < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ False ”

noncomputable def minimal_representation_safety_wit_9 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_10 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (j < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_11 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i ≠ j)) (PreH12 : ((0 : Int) <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best)) (PreH15 : (MRCandidateState l best i j)) (PreH16 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((j + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + k)) ”

noncomputable def minimal_representation_safety_wit_12 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i ≠ j)) (PreH12 : ((0 : Int) <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best)) (PreH15 : (MRCandidateState l best i j)) (PreH16 : (MRRotationPrefixEq l i j k)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((i + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + k)) ”

noncomputable def minimal_representation_safety_wit_13 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) = (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i ≠ j)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) (PreH17 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def minimal_representation_safety_wit_14 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k ≠ n_pre)) (PreH2 : (k >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i ≠ j)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) (PreH17 : (MRRotationPrefixEq l i j k)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ False ”

noncomputable def minimal_representation_safety_wit_15 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k = n_pre)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) (PreH18 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ False ”

noncomputable def minimal_representation_safety_wit_16 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k ≠ n_pre)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) (PreH18 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((j + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + k)) ”

noncomputable def minimal_representation_safety_wit_17 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k ≠ n_pre)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) (PreH18 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((i + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + k)) ”

noncomputable def minimal_representation_safety_wit_18 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) > (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k ≠ n_pre)) (PreH3 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((0 : Int) <= best)) (PreH9 : (best < n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i ≠ j)) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best)) (PreH18 : (MRCandidateState l best i j)) (PreH19 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (((i + k) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i + k) + 1)) ”

noncomputable def minimal_representation_safety_wit_19 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) > (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k ≠ n_pre)) (PreH3 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((0 : Int) <= best)) (PreH9 : (best < n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i ≠ j)) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best)) (PreH18 : (MRCandidateState l best i j)) (PreH19 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((i + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + k)) ”

noncomputable def minimal_representation_safety_wit_20 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) > (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k ≠ n_pre)) (PreH3 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((0 : Int) <= best)) (PreH9 : (best < n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i ≠ j)) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best)) (PreH18 : (MRCandidateState l best i j)) (PreH19 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def minimal_representation_safety_wit_21 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (((i + k) + 1) = j)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) > (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k ≠ n_pre)) (PreH4 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best < n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i ≠ j)) (PreH16 : ((0 : Int) <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best)) (PreH19 : (MRCandidateState l best i j)) (PreH20 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (((i + k) + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((((i + k) + 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i + k) + 1) + 1)) ”

noncomputable def minimal_representation_safety_wit_22 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) <= (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k ≠ n_pre)) (PreH3 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((0 : Int) <= best)) (PreH9 : (best < n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i ≠ j)) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best)) (PreH18 : (MRCandidateState l best i j)) (PreH19 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (((j + k) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((j + k) + 1)) ”

noncomputable def minimal_representation_safety_wit_23 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) <= (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k ≠ n_pre)) (PreH3 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((0 : Int) <= best)) (PreH9 : (best < n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i ≠ j)) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best)) (PreH18 : (MRCandidateState l best i j)) (PreH19 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((j + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + k)) ”

noncomputable def minimal_representation_safety_wit_24 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) <= (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k ≠ n_pre)) (PreH3 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH4 : (k < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 1000)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((0 : Int) <= best)) (PreH9 : (best < n_pre)) (PreH10 : ((0 : Int) <= i)) (PreH11 : (i < n_pre)) (PreH12 : ((0 : Int) <= j)) (PreH13 : (j < n_pre)) (PreH14 : (i ≠ j)) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= n_pre)) (PreH17 : (MRFirstMinimalRotationAt l best)) (PreH18 : (MRCandidateState l best i j)) (PreH19 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def minimal_representation_safety_wit_25 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (i = ((j + k) + 1))) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) <= (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k ≠ n_pre)) (PreH4 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best < n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i ≠ j)) (PreH16 : ((0 : Int) <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best)) (PreH19 : (MRCandidateState l best i j)) (PreH20 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (((j + k) + 1)))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((((j + k) + 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((j + k) + 1) + 1)) ”

noncomputable def minimal_representation_safety_wit_26 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (i))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_27 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (i))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_28 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_29 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (j))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def minimal_representation_safety_wit_30 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (best))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) k (sublist ((0 : Int)) (k) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre k n_pre)
|--
  “ ((best + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (best + k)) ”

noncomputable def minimal_representation_safety_wit_31 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg out_pre (0 : Int) (k + 1) ((sublist ((0 : Int)) (k) ((MRRotation (l) (best)))) ++ ((Znth (best + k) (l ++ l) (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (k + 1) n_pre)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "p" ) )) # Int |-> (best))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def minimal_representation_entail_wit_1 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((0 : Int) <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.undef_full ( &( "b" ) ) 2000)
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (0 : Int) n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + (0 : Int)) (sublist ((0 : Int)) ((0 : Int)) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + (0 : Int)) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((0 : Int) <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.undef_full ( &( "b" ) ) 2000)
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) (l)) = (@List.nil Int)) ”
  &&  (intArray.undef_seg ( &( "b" ) ) (0 : Int) n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + (0 : Int)) (sublist ((0 : Int)) ((0 : Int)) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + (0 : Int)) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
)

noncomputable def minimal_representation_entail_wit_1_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((0 : Int) <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.undef_full ( &( "b" ) ) 2000)
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) (l)) = (@List.nil Int)) ”

noncomputable def minimal_representation_entail_wit_1_split_goal_spatial : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((0 : Int) <= best)) (PreH5 : (best < n_pre)) (PreH6 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.undef_full ( &( "b" ) ) 2000)
|--
  (intArray.undef_seg ( &( "b" ) ) (0 : Int) n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + (0 : Int)) (sublist ((0 : Int)) ((0 : Int)) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + (0 : Int)) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)

noncomputable def minimal_representation_entail_wit_2 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg ( &( "b" ) ) n_pre ((n_pre + p) + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) ((n_pre + p) + 1) (2 * n_pre))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= (p + 1)) ” &&
  “ ((p + 1) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) (sublist ((0 : Int)) ((p + 1)) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + (p + 1)) (sublist ((0 : Int)) ((p + 1)) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + (p + 1)) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg ( &( "b" ) ) n_pre ((n_pre + p) + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
|--
  “ (((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((p + 1)) (l))) ”
  &&  (intArray.seg ( &( "b" ) ) n_pre (n_pre + (p + 1)) (sublist ((0 : Int)) ((p + 1)) (l)))
)

noncomputable def minimal_representation_entail_wit_2_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg ( &( "b" ) ) n_pre ((n_pre + p) + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
|--
  “ (((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((p + 1)) (l))) ”

noncomputable def minimal_representation_entail_wit_2_split_goal_spatial : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg ( &( "b" ) ) n_pre ((n_pre + p) + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
|--
  (intArray.seg ( &( "b" ) ) n_pre (n_pre + (p + 1)) (sublist ((0 : Int)) ((p + 1)) (l)))

noncomputable def minimal_representation_entail_wit_3 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "p" ) )) # Int |-> (p))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) p n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < (2 * n_pre)) ” &&
  “ ((0 : Int) ≠ 1) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best (0 : Int) 1) ”
  &&  ((( &( "p" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))
  ||
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < (2 * n_pre)) ” &&
  “ ((0 : Int) ≠ 1) ” &&
  “ (1 < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best (0 : Int) 1) ”
  &&  ((( &( "p" ) )) # Int |-> (n_pre))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))

noncomputable def minimal_representation_entail_wit_4_1 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i j) ” &&
  “ (MRRotationPrefixEq l i j (0 : Int)) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  TT && emp 
|--
  “ (MRRotationPrefixEq l i j (0 : Int)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_4_1_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  (MRRotationPrefixEq l i j (0 : Int))

noncomputable def minimal_representation_entail_wit_4_2 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (j < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i j) ” &&
  “ (MRRotationPrefixEq l i j (0 : Int)) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (j < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  TT && emp 
|--
  “ (MRRotationPrefixEq l i j (0 : Int)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_4_2_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j < n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (j < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  (MRRotationPrefixEq l i j (0 : Int))

noncomputable def minimal_representation_entail_wit_5 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) = (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i ≠ j)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) (PreH17 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i j) ” &&
  “ (MRRotationPrefixEq l i j (k + 1)) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) = (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i ≠ j)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) (PreH17 : (MRRotationPrefixEq l i j k)) ,
  TT && emp 
|--
  “ (MRRotationPrefixEq l i j (k + 1)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_5_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : ((Znth (i + k) (l ++ l) (0 : Int)) = (Znth (j + k) (l ++ l) (0 : Int)))) (PreH2 : (k < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i ≠ j)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) (PreH17 : (MRRotationPrefixEq l i j k)) ,
  (MRRotationPrefixEq l i j (k + 1))

noncomputable def minimal_representation_entail_wit_6_1 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (((i + k) + 1) = j)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) > (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k ≠ n_pre)) (PreH4 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best < n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i ≠ j)) (PreH16 : ((0 : Int) <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best)) (PreH19 : (MRCandidateState l best i j)) (PreH20 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= (((i + k) + 1) + 1)) ” &&
  “ ((((i + k) + 1) + 1) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ ((((i + k) + 1) + 1) ≠ j) ” &&
  “ ((((i + k) + 1) + 1) < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best (((i + k) + 1) + 1) j) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))
  ||
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= (((i + k) + 1) + 1)) ” &&
  “ ((((i + k) + 1) + 1) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ ((((i + k) + 1) + 1) ≠ j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best (((i + k) + 1) + 1) j) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))

noncomputable def minimal_representation_entail_wit_6_2 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (((i + k) + 1) ≠ j)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) > (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k ≠ n_pre)) (PreH4 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best < n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i ≠ j)) (PreH16 : ((0 : Int) <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best)) (PreH19 : (MRCandidateState l best i j)) (PreH20 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= ((i + k) + 1)) ” &&
  “ (((i + k) + 1) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (((i + k) + 1) ≠ j) ” &&
  “ (((i + k) + 1) < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best ((i + k) + 1) j) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))
  ||
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= ((i + k) + 1)) ” &&
  “ (((i + k) + 1) < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (((i + k) + 1) ≠ j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best ((i + k) + 1) j) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))

noncomputable def minimal_representation_entail_wit_6_3 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (i = ((j + k) + 1))) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) <= (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k ≠ n_pre)) (PreH4 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best < n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i ≠ j)) (PreH16 : ((0 : Int) <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best)) (PreH19 : (MRCandidateState l best i j)) (PreH20 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= (((j + k) + 1) + 1)) ” &&
  “ ((((j + k) + 1) + 1) < (2 * n_pre)) ” &&
  “ (i ≠ (((j + k) + 1) + 1)) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i (((j + k) + 1) + 1)) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))
  ||
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= (((j + k) + 1) + 1)) ” &&
  “ ((((j + k) + 1) + 1) < (2 * n_pre)) ” &&
  “ (i ≠ (((j + k) + 1) + 1)) ” &&
  “ ((((j + k) + 1) + 1) < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i (((j + k) + 1) + 1)) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))

noncomputable def minimal_representation_entail_wit_6_4 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (i ≠ ((j + k) + 1))) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) <= (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k ≠ n_pre)) (PreH4 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH5 : (k < n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 1000)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((0 : Int) <= best)) (PreH10 : (best < n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= j)) (PreH14 : (j < n_pre)) (PreH15 : (i ≠ j)) (PreH16 : ((0 : Int) <= k)) (PreH17 : (k <= n_pre)) (PreH18 : (MRFirstMinimalRotationAt l best)) (PreH19 : (MRCandidateState l best i j)) (PreH20 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= ((j + k) + 1)) ” &&
  “ (((j + k) + 1) < (2 * n_pre)) ” &&
  “ (i ≠ ((j + k) + 1)) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i ((j + k) + 1)) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))
  ||
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= ((j + k) + 1)) ” &&
  “ (((j + k) + 1) < (2 * n_pre)) ” &&
  “ (i ≠ ((j + k) + 1)) ” &&
  “ (((j + k) + 1) < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k < n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i ((j + k) + 1)) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))

noncomputable def minimal_representation_entail_wit_7_1 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ ((i < j) -> (i = best)) ” &&
  “ ((i >= j) -> (j = best)) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) ,
  TT && emp 
|--
  “ ((i >= j) -> (j = best)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_7_1_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k < n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) ,
  ((i >= j) -> (j = best))

noncomputable def minimal_representation_entail_wit_7_2 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ ((i < j) -> (i = best)) ” &&
  “ ((i >= j) -> (j = best)) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  TT && emp 
|--
  “ ((i < j) -> (i = best)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_7_2_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (j >= n_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < (2 * n_pre))) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < (2 * n_pre))) (PreH12 : (i ≠ j)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k < n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) ,
  ((i < j) -> (i = best))

noncomputable def minimal_representation_entail_wit_7_3 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k = n_pre)) (PreH2 : (k >= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((0 : Int) <= best)) (PreH7 : (best < n_pre)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j < n_pre)) (PreH12 : (i ≠ j)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : (MRFirstMinimalRotationAt l best)) (PreH16 : (MRCandidateState l best i j)) (PreH17 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ ((i < j) -> (i = best)) ” &&
  “ ((i >= j) -> (j = best)) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))
  ||
  (“ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ ((i < j) -> (i = best)) ” &&
  “ ((i >= j) -> (j = best)) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre))

noncomputable def minimal_representation_entail_wit_8_1 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "p" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  ((( &( "p" ) )) # Int |-> (best))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre (0 : Int) n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_8_1_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int))

noncomputable def minimal_representation_entail_wit_8_2 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "p" ) )) # Int |-> (i))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  ((( &( "p" ) )) # Int |-> (best))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre (0 : Int) n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_8_2_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i < j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int))

noncomputable def minimal_representation_entail_wit_8_3 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "p" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  ((( &( "p" ) )) # Int |-> (best))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre (0 : Int) n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_8_3_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (j < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int))

noncomputable def minimal_representation_entail_wit_8_4 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((( &( "p" ) )) # Int |-> (j))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  ((( &( "p" ) )) # Int |-> (best))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre (0 : Int) n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  TT && emp 
|--
  “ ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_8_4_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (i : Int) (j : Int) (k : Int) (PreH1 : (i >= j)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < (2 * n_pre))) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < (2 * n_pre))) (PreH11 : (i ≠ j)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= k)) (PreH14 : (k <= n_pre)) (PreH15 : ((i < j) -> (i = best))) (PreH16 : ((i >= j) -> (j = best))) (PreH17 : (MRFirstMinimalRotationAt l best)) ,
  ((sublist ((0 : Int)) ((0 : Int)) ((MRRotation (l) (best)))) = (@List.nil Int))

noncomputable def minimal_representation_entail_wit_9 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg out_pre (0 : Int) (k + 1) ((sublist ((0 : Int)) (k) ((MRRotation (l) (best)))) ++ ((Znth (best + k) (l ++ l) (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (k + 1) n_pre)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) (k + 1) (sublist ((0 : Int)) ((k + 1)) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre (k + 1) n_pre)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  TT && emp 
|--
  “ (((sublist ((0 : Int)) (k) ((MRRotation (l) (best)))) ++ ((Znth (best + k) (l ++ l) (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((k + 1)) ((MRRotation (l) (best))))) ”
  &&  emp
)

noncomputable def minimal_representation_entail_wit_9_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (((sublist ((0 : Int)) (k) ((MRRotation (l) (best)))) ++ ((Znth (best + k) (l ++ l) (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((k + 1)) ((MRRotation (l) (best)))))

noncomputable def minimal_representation_entail_wit_10 : Prop :=
  (
forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) k (sublist ((0 : Int)) (k) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre k n_pre)
|--
  “ ((0 : Int) <= i) ” &&
  “ ((0 : Int) <= j) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full out_pre n_pre (MRRotation (l) (best)))
  ** (intArray.undef_full ( &( "b" ) ) 2000)
) \/
(
forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
|--
  “ ((sublist ((0 : Int)) (k) ((MRRotation (l) (best)))) = (MRRotation (l) (best))) ”
  &&  (intArray.undef_full ( &( "b" ) ) 2000)
)

noncomputable def minimal_representation_entail_wit_10_split_goal_1 : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
|--
  “ ((sublist ((0 : Int)) (k) ((MRRotation (l) (best)))) = (MRRotation (l) (best))) ”

noncomputable def minimal_representation_entail_wit_10_split_goal_spatial : Prop :=
  forall (best : Int) (l : (List Int)) (n_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
|--
  (intArray.undef_full ( &( "b" ) ) 2000)

noncomputable def minimal_representation_return_wit_1 : Prop :=
  forall (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (i : Int) (j : Int) (k : Int) (p : Int) (PreH1 : ((0 : Int) <= i)) (PreH2 : ((0 : Int) <= j)) (PreH3 : ((0 : Int) <= k)) (PreH4 : (MRFirstMinimalRotationAt l p)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full out_pre n_pre (MRRotation (l) (p)))
|--
  “ (MRFirstMinimalRotationAt l p) ”
  &&  (intArray.full a_pre n_pre l)
  ** (intArray.full out_pre n_pre (MRRotation (l) (p)))

noncomputable def minimal_representation_partial_solve_wit_1 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) p n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (p < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= p) ” &&
  “ (p <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (((a_pre + (p * sizeof(INT)))) # Int |-> ((Znth p l (0 : Int))))
  ** (intArray.missing_i a_pre p (0 : Int) n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) p n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_2 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) p n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (p < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= p) ” &&
  “ (p <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (((( &( "b" ) ) + (p * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) p (sublist ((0 : Int)) (p) (l)))
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_3 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (p < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= p) ” &&
  “ (p <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (((a_pre + (p * sizeof(INT)))) # Int |-> ((Znth p l (0 : Int))))
  ** (intArray.missing_i a_pre p (0 : Int) n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_4 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (p : Int) (PreH1 : (p < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= p)) (PreH8 : (p <= n_pre)) (PreH9 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (n_pre + p) (2 * n_pre))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (p < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= p) ” &&
  “ (p <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (((( &( "b" ) ) + ((n_pre + p) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "b" ) ) ((n_pre + p) + 1) (2 * n_pre))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.seg ( &( "b" ) ) (0 : Int) (p + 1) ((sublist ((0 : Int)) (p) (l)) ++ ((Znth p l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "b" ) ) (p + 1) n_pre)
  ** (intArray.seg ( &( "b" ) ) n_pre (n_pre + p) (sublist ((0 : Int)) (p) (l)))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_5 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i ≠ j)) (PreH12 : ((0 : Int) <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best)) (PreH15 : (MRCandidateState l best i j)) (PreH16 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i j) ” &&
  “ (MRRotationPrefixEq l i j k) ”
  &&  (((( &( "b" ) ) + ((i + k) * sizeof(INT)))) # Int |-> ((Znth (i + k) (l ++ l) (0 : Int))))
  ** (intArray.missing_i ( &( "b" ) ) (i + k) (0 : Int) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_6 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j < n_pre)) (PreH11 : (i ≠ j)) (PreH12 : ((0 : Int) <= k)) (PreH13 : (k <= n_pre)) (PreH14 : (MRFirstMinimalRotationAt l best)) (PreH15 : (MRCandidateState l best i j)) (PreH16 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i j) ” &&
  “ (MRRotationPrefixEq l i j k) ”
  &&  (((( &( "b" ) ) + ((j + k) * sizeof(INT)))) # Int |-> ((Znth (j + k) (l ++ l) (0 : Int))))
  ** (intArray.missing_i ( &( "b" ) ) (j + k) (0 : Int) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_7 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k ≠ n_pre)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) (PreH18 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (k ≠ n_pre) ” &&
  “ ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int))) ” &&
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i j) ” &&
  “ (MRRotationPrefixEq l i j k) ”
  &&  (((( &( "b" ) ) + ((i + k) * sizeof(INT)))) # Int |-> ((Znth (i + k) (l ++ l) (0 : Int))))
  ** (intArray.missing_i ( &( "b" ) ) (i + k) (0 : Int) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_8 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k ≠ n_pre)) (PreH2 : ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int)))) (PreH3 : (k < n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 1000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < n_pre)) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < n_pre)) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) (PreH17 : (MRCandidateState l best i j)) (PreH18 : (MRRotationPrefixEq l i j k)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)
|--
  “ (k ≠ n_pre) ” &&
  “ ((Znth (i + k) (l ++ l) (0 : Int)) ≠ (Znth (j + k) (l ++ l) (0 : Int))) ” &&
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ” &&
  “ (MRCandidateState l best i j) ” &&
  “ (MRRotationPrefixEq l i j k) ”
  &&  (((( &( "b" ) ) + ((j + k) * sizeof(INT)))) # Int |-> ((Znth (j + k) (l ++ l) (0 : Int))))
  ** (intArray.missing_i ( &( "b" ) ) (j + k) (0 : Int) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.undef_full out_pre n_pre)

noncomputable def minimal_representation_partial_solve_wit_9 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full a_pre n_pre l)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) k (sublist ((0 : Int)) (k) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre k n_pre)
|--
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (((( &( "b" ) ) + ((best + k) * sizeof(INT)))) # Int |-> ((Znth (best + k) (l ++ l) (0 : Int))))
  ** (intArray.missing_i ( &( "b" ) ) (best + k) (0 : Int) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) k (sublist ((0 : Int)) (k) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre k n_pre)

noncomputable def minimal_representation_partial_solve_wit_10 : Prop :=
  forall (best : Int) (l : (List Int)) (a_pre : Int) (n_pre : Int) (out_pre : Int) (k : Int) (j : Int) (i : Int) (PreH1 : (k < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((0 : Int) <= best)) (PreH6 : (best < n_pre)) (PreH7 : ((0 : Int) <= best)) (PreH8 : (best < n_pre)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i < (2 * n_pre))) (PreH11 : ((0 : Int) <= j)) (PreH12 : (j < (2 * n_pre))) (PreH13 : (i ≠ j)) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= n_pre)) (PreH16 : (MRFirstMinimalRotationAt l best)) ,
  (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) k (sublist ((0 : Int)) (k) ((MRRotation (l) (best)))))
  ** (intArray.undef_seg out_pre k n_pre)
|--
  “ (k < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (2 * n_pre)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < (2 * n_pre)) ” &&
  “ (i ≠ j) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= n_pre) ” &&
  “ (MRFirstMinimalRotationAt l best) ”
  &&  (((out_pre + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (k + 1) n_pre)
  ** (intArray.full ( &( "b" ) ) (2 * n_pre) (l ++ l))
  ** (intArray.full a_pre n_pre l)
  ** (intArray.undef_seg ( &( "b" ) ) (2 * n_pre) 2000)
  ** (intArray.seg out_pre (0 : Int) k (sublist ((0 : Int)) (k) ((MRRotation (l) (best)))))


structure VC_Correct : Type where
  proof_of_minimal_representation_safety_wit_1 : minimal_representation_safety_wit_1
  proof_of_minimal_representation_safety_wit_2 : minimal_representation_safety_wit_2
  proof_of_minimal_representation_safety_wit_3 : minimal_representation_safety_wit_3
  proof_of_minimal_representation_safety_wit_4 : minimal_representation_safety_wit_4
  proof_of_minimal_representation_safety_wit_5 : minimal_representation_safety_wit_5
  proof_of_minimal_representation_safety_wit_6 : minimal_representation_safety_wit_6
  proof_of_minimal_representation_safety_wit_7 : minimal_representation_safety_wit_7
  proof_of_minimal_representation_safety_wit_8 : minimal_representation_safety_wit_8
  proof_of_minimal_representation_safety_wit_9 : minimal_representation_safety_wit_9
  proof_of_minimal_representation_safety_wit_10 : minimal_representation_safety_wit_10
  proof_of_minimal_representation_safety_wit_11 : minimal_representation_safety_wit_11
  proof_of_minimal_representation_safety_wit_12 : minimal_representation_safety_wit_12
  proof_of_minimal_representation_safety_wit_13 : minimal_representation_safety_wit_13
  proof_of_minimal_representation_safety_wit_14 : minimal_representation_safety_wit_14
  proof_of_minimal_representation_safety_wit_15 : minimal_representation_safety_wit_15
  proof_of_minimal_representation_safety_wit_16 : minimal_representation_safety_wit_16
  proof_of_minimal_representation_safety_wit_17 : minimal_representation_safety_wit_17
  proof_of_minimal_representation_safety_wit_18 : minimal_representation_safety_wit_18
  proof_of_minimal_representation_safety_wit_19 : minimal_representation_safety_wit_19
  proof_of_minimal_representation_safety_wit_20 : minimal_representation_safety_wit_20
  proof_of_minimal_representation_safety_wit_21 : minimal_representation_safety_wit_21
  proof_of_minimal_representation_safety_wit_22 : minimal_representation_safety_wit_22
  proof_of_minimal_representation_safety_wit_23 : minimal_representation_safety_wit_23
  proof_of_minimal_representation_safety_wit_24 : minimal_representation_safety_wit_24
  proof_of_minimal_representation_safety_wit_25 : minimal_representation_safety_wit_25
  proof_of_minimal_representation_safety_wit_26 : minimal_representation_safety_wit_26
  proof_of_minimal_representation_safety_wit_27 : minimal_representation_safety_wit_27
  proof_of_minimal_representation_safety_wit_28 : minimal_representation_safety_wit_28
  proof_of_minimal_representation_safety_wit_29 : minimal_representation_safety_wit_29
  proof_of_minimal_representation_safety_wit_30 : minimal_representation_safety_wit_30
  proof_of_minimal_representation_safety_wit_31 : minimal_representation_safety_wit_31
  proof_of_minimal_representation_return_wit_1 : minimal_representation_return_wit_1
  proof_of_minimal_representation_partial_solve_wit_1 : minimal_representation_partial_solve_wit_1
  proof_of_minimal_representation_partial_solve_wit_2 : minimal_representation_partial_solve_wit_2
  proof_of_minimal_representation_partial_solve_wit_3 : minimal_representation_partial_solve_wit_3
  proof_of_minimal_representation_partial_solve_wit_4 : minimal_representation_partial_solve_wit_4
  proof_of_minimal_representation_partial_solve_wit_5 : minimal_representation_partial_solve_wit_5
  proof_of_minimal_representation_partial_solve_wit_6 : minimal_representation_partial_solve_wit_6
  proof_of_minimal_representation_partial_solve_wit_7 : minimal_representation_partial_solve_wit_7
  proof_of_minimal_representation_partial_solve_wit_8 : minimal_representation_partial_solve_wit_8
  proof_of_minimal_representation_partial_solve_wit_9 : minimal_representation_partial_solve_wit_9
  proof_of_minimal_representation_partial_solve_wit_10 : minimal_representation_partial_solve_wit_10
  proof_of_minimal_representation_entail_wit_1 : minimal_representation_entail_wit_1
  proof_of_minimal_representation_entail_wit_2 : minimal_representation_entail_wit_2
  proof_of_minimal_representation_entail_wit_3 : minimal_representation_entail_wit_3
  proof_of_minimal_representation_entail_wit_4_1 : minimal_representation_entail_wit_4_1
  proof_of_minimal_representation_entail_wit_4_2 : minimal_representation_entail_wit_4_2
  proof_of_minimal_representation_entail_wit_5 : minimal_representation_entail_wit_5
  proof_of_minimal_representation_entail_wit_6_1 : minimal_representation_entail_wit_6_1
  proof_of_minimal_representation_entail_wit_6_2 : minimal_representation_entail_wit_6_2
  proof_of_minimal_representation_entail_wit_6_3 : minimal_representation_entail_wit_6_3
  proof_of_minimal_representation_entail_wit_6_4 : minimal_representation_entail_wit_6_4
  proof_of_minimal_representation_entail_wit_7_1 : minimal_representation_entail_wit_7_1
  proof_of_minimal_representation_entail_wit_7_2 : minimal_representation_entail_wit_7_2
  proof_of_minimal_representation_entail_wit_7_3 : minimal_representation_entail_wit_7_3
  proof_of_minimal_representation_entail_wit_8_1 : minimal_representation_entail_wit_8_1
  proof_of_minimal_representation_entail_wit_8_2 : minimal_representation_entail_wit_8_2
  proof_of_minimal_representation_entail_wit_8_3 : minimal_representation_entail_wit_8_3
  proof_of_minimal_representation_entail_wit_8_4 : minimal_representation_entail_wit_8_4
  proof_of_minimal_representation_entail_wit_9 : minimal_representation_entail_wit_9
  proof_of_minimal_representation_entail_wit_10 : minimal_representation_entail_wit_10

end SimpleC.EE.LLM_bench.Algorithms.minimal_representation.minimal_representation_goal
