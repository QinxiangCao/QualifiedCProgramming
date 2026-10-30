import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_lib
open SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance kings_game_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def swap_ministers_safety_wit_1 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  ((( &( "tmp_left" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
  ** (intArray.full a_pre (2 * n_pre) flat)
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_ministers_safety_wit_2 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  ((( &( "tmp_left" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
  ** (intArray.full a_pre (2 * n_pre) flat)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_3 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  ((( &( "tmp_right" ) )) # Int |->_)
  ** (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * i_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i_pre) + 1)) ”

noncomputable def swap_ministers_safety_wit_4 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  ((( &( "tmp_right" ) )) # Int |->_)
  ** (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_ministers_safety_wit_5 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  ((( &( "tmp_right" ) )) # Int |->_)
  ** (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_6 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  ((( &( "tmp_right" ) )) # Int |->_)
  ** (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_ministers_safety_wit_7 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_ministers_safety_wit_8 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_9 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_ministers_safety_wit_10 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_11 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * i_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i_pre) + 1)) ”

noncomputable def swap_ministers_safety_wit_12 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_ministers_safety_wit_13 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_14 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_ministers_safety_wit_15 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * j_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * j_pre) + 1)) ”

noncomputable def swap_ministers_safety_wit_16 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_ministers_safety_wit_17 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_18 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_ministers_safety_wit_19 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_ministers_safety_wit_20 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_21 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * j_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * j_pre) + 1)) ”

noncomputable def swap_ministers_safety_wit_22 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_ministers_safety_wit_23 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_ministers_safety_wit_24 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_right" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_left" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_ministers_return_wit_1 : Prop :=
  (
forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth (((2 * j_pre) + 1)) ((Znth ((2 * i_pre) + 1) flat (0 : Int))) ((replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))))
|--
  “ (FlatMinisters (minister_swap_flat (flat) (i_pre) (j_pre)) (minister_swap (ps) (i_pre) (j_pre))) ” &&
  “ (MinisterPermutation ps (minister_swap (ps) (i_pre) (j_pre))) ”
  &&  (intArray.full a_pre (2 * n_pre) (minister_swap_flat (flat) (i_pre) (j_pre)))
) \/
(
forall (ps : (List minister)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  TT && emp 
|--
  “ (MinisterPermutation ps (minister_swap (ps) (i_pre) (j_pre))) ” &&
  “ (FlatMinisters (minister_swap_flat (flat) (i_pre) (j_pre)) (minister_swap (ps) (i_pre) (j_pre))) ” &&
  “ ((replace_Znth (((2 * j_pre) + 1)) ((Znth ((2 * i_pre) + 1) flat (0 : Int))) ((replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))) = (minister_swap_flat (flat) (i_pre) (j_pre))) ”
  &&  emp
)

noncomputable def swap_ministers_return_wit_1_split_goal_1 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (MinisterPermutation ps (minister_swap (ps) (i_pre) (j_pre)))

noncomputable def swap_ministers_return_wit_1_split_goal_2 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (FlatMinisters (minister_swap_flat (flat) (i_pre) (j_pre)) (minister_swap (ps) (i_pre) (j_pre)))

noncomputable def swap_ministers_return_wit_1_split_goal_3 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  ((replace_Znth (((2 * j_pre) + 1)) ((Znth ((2 * i_pre) + 1) flat (0 : Int))) ((replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))) = (minister_swap_flat (flat) (i_pre) (j_pre)))

noncomputable def swap_ministers_partial_solve_wit_1 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + ((2 * i_pre) * sizeof(INT)))) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** (intArray.missing_i a_pre (2 * i_pre) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_ministers_partial_solve_wit_2 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + (((2 * i_pre) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** (intArray.missing_i a_pre ((2 * i_pre) + 1) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_ministers_partial_solve_wit_3 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + ((2 * j_pre) * sizeof(INT)))) # Int |-> ((Znth (2 * j_pre) flat (0 : Int))))
  ** (intArray.missing_i a_pre (2 * j_pre) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_ministers_partial_solve_wit_4 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + ((2 * i_pre) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre (2 * i_pre) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_ministers_partial_solve_wit_5 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + (((2 * j_pre) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))))
  ** (intArray.missing_i a_pre ((2 * j_pre) + 1) (0 : Int) (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))

noncomputable def swap_ministers_partial_solve_wit_6 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + (((2 * i_pre) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre ((2 * i_pre) + 1) (0 : Int) (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))

noncomputable def swap_ministers_partial_solve_wit_7 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + ((2 * j_pre) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre (2 * j_pre) (0 : Int) (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))

noncomputable def swap_ministers_partial_solve_wit_8 : Prop :=
  forall (ps : (List minister)) (flat : (List Int)) (a_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (ps)) = n_pre)) (PreH8 : (FlatMinisters flat ps)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps)))) ,
  (intArray.full a_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (ps)) = n_pre) ” &&
  “ (FlatMinisters flat ps) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (ps))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (ps))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (ps))) ”
  &&  (((a_pre + (((2 * j_pre) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i a_pre ((2 * j_pre) + 1) (0 : Int) (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))

noncomputable def kings_game_safety_wit_1 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.undef_full ans_pre (2 * n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def kings_game_safety_wit_2 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= (2 * n_pre))) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))
  ** (intArray.undef_seg ans_pre k (2 * n_pre))
|--
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * n_pre)) ”

noncomputable def kings_game_safety_wit_3 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= k)) (PreH15 : (k <= (2 * n_pre))) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))
  ** (intArray.undef_seg ans_pre k (2 * n_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def kings_game_safety_wit_4 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (k < (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  (intArray.seg ans_pre (0 : Int) (k + 1) ((sublist ((0 : Int)) (k) (input_flat)) ++ ((Znth k input_flat (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ans_pre (k + 1) (2 * n_pre))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def kings_game_safety_wit_5 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (k >= (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  ((( &( "pass" ) )) # Int |->_)
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))
  ** (intArray.undef_seg ans_pre k (2 * n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def kings_game_safety_wit_6 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (pass : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH13 : ((0 : Int) <= pass)) (PreH14 : (pass <= (n_pre - 1))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur)) (PreH17 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH18 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH20 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH21 : (MinisterPermutation input cur)) (PreH22 : (BubbleOuterProperty cur n_pre pass)) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def kings_game_safety_wit_7 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (pass : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH13 : ((0 : Int) <= pass)) (PreH14 : (pass <= (n_pre - 1))) (PreH15 : ((Zlength (cur)) = n_pre)) (PreH16 : (FlatMinisters flat_cur cur)) (PreH17 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH18 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH20 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH21 : (MinisterPermutation input cur)) (PreH22 : (BubbleOuterProperty cur n_pre pass)) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def kings_game_safety_wit_8 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (pass : Int) (PreH1 : (pass < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass <= (n_pre - 1))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH22 : (MinisterPermutation input cur)) (PreH23 : (BubbleOuterProperty cur n_pre pass)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def kings_game_safety_wit_9 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH13 : ((0 : Int) <= pass)) (PreH14 : (pass < (n_pre - 1))) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= ((n_pre - 1) - pass))) (PreH17 : ((Zlength (cur)) = n_pre)) (PreH18 : (FlatMinisters flat_cur cur)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH20 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH23 : (MinisterPermutation input cur)) (PreH24 : (BubbleOuterProperty cur n_pre pass)) (PreH25 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ (((n_pre - 1) - pass) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((n_pre - 1) - pass)) ”

noncomputable def kings_game_safety_wit_10 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH13 : ((0 : Int) <= pass)) (PreH14 : (pass < (n_pre - 1))) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= ((n_pre - 1) - pass))) (PreH17 : ((Zlength (cur)) = n_pre)) (PreH18 : (FlatMinisters flat_cur cur)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH20 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH23 : (MinisterPermutation input cur)) (PreH24 : (BubbleOuterProperty cur n_pre pass)) (PreH25 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def kings_game_safety_wit_11 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH13 : ((0 : Int) <= pass)) (PreH14 : (pass < (n_pre - 1))) (PreH15 : ((0 : Int) <= j)) (PreH16 : (j <= ((n_pre - 1) - pass))) (PreH17 : ((Zlength (cur)) = n_pre)) (PreH18 : (FlatMinisters flat_cur cur)) (PreH19 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH20 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH23 : (MinisterPermutation input cur)) (PreH24 : (BubbleOuterProperty cur n_pre pass)) (PreH25 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def kings_game_safety_wit_12 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "left1" ) )) # Int |->_)
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ ((2 * j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j)) ”

noncomputable def kings_game_safety_wit_13 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "left1" ) )) # Int |->_)
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def kings_game_safety_wit_14 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right1" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((2 * j) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * j) + 1)) ”

noncomputable def kings_game_safety_wit_15 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right1" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((2 * j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j)) ”

noncomputable def kings_game_safety_wit_16 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right1" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def kings_game_safety_wit_17 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right1" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def kings_game_safety_wit_18 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "left2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((2 * (j + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * (j + 1))) ”

noncomputable def kings_game_safety_wit_19 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "left2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def kings_game_safety_wit_20 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "left2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def kings_game_safety_wit_21 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "left2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def kings_game_safety_wit_22 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((2 * (j + 1)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * (j + 1)) + 1)) ”

noncomputable def kings_game_safety_wit_23 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((2 * (j + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * (j + 1))) ”

noncomputable def kings_game_safety_wit_24 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def kings_game_safety_wit_25 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def kings_game_safety_wit_26 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def kings_game_safety_wit_27 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "right2" ) )) # Int |->_)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def kings_game_safety_wit_28 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int)))) ”
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int)))) ”
)

noncomputable def kings_game_safety_wit_28_split_goal_1 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))) <= INT_MAX) ”

noncomputable def kings_game_safety_wit_28_split_goal_2 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((INT_MIN) <= ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int)))) ”

noncomputable def kings_game_safety_wit_29 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int)))) ”
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int)))) ”
)

noncomputable def kings_game_safety_wit_29_split_goal_1 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) <= INT_MAX) ”

noncomputable def kings_game_safety_wit_29_split_goal_2 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((INT_MIN) <= ((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int)))) ”

noncomputable def kings_game_safety_wit_30 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))) (PreH2 : (j < ((n_pre - 1) - pass))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= pass)) (PreH16 : (pass < (n_pre - 1))) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= ((n_pre - 1) - pass))) (PreH19 : ((Zlength (cur)) = n_pre)) (PreH20 : (FlatMinisters flat_cur cur)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH25 : (MinisterPermutation input cur)) (PreH26 : (BubbleOuterProperty cur n_pre pass)) (PreH27 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def kings_game_safety_wit_31 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))) (PreH2 : (j < ((n_pre - 1) - pass))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= pass)) (PreH16 : (pass < (n_pre - 1))) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= ((n_pre - 1) - pass))) (PreH19 : ((Zlength (cur)) = n_pre)) (PreH20 : (FlatMinisters flat_cur cur)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH25 : (MinisterPermutation input cur)) (PreH26 : (BubbleOuterProperty cur n_pre pass)) (PreH27 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def kings_game_safety_wit_32 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (FlatMinisters (minister_swap_flat (flat_cur) (j) ((j + 1))) (minister_swap (cur) (j) ((j + 1))))) (PreH2 : (MinisterPermutation cur (minister_swap (cur) (j) ((j + 1))))) (PreH3 : (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))) (PreH4 : (j < ((n_pre - 1) - pass))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : (1 <= king_left_pre)) (PreH8 : (king_left_pre <= 10)) (PreH9 : (1 <= king_right_pre)) (PreH10 : (king_right_pre <= 10)) (PreH11 : ((Zlength (input)) = n_pre)) (PreH12 : (FlatMinisters input_flat input)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH16 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH17 : ((0 : Int) <= pass)) (PreH18 : (pass < (n_pre - 1))) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= ((n_pre - 1) - pass))) (PreH21 : ((Zlength (cur)) = n_pre)) (PreH22 : (FlatMinisters flat_cur cur)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH26 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH27 : (MinisterPermutation input cur)) (PreH28 : (BubbleOuterProperty cur n_pre pass)) (PreH29 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) (minister_swap_flat (flat_cur) (j) ((j + 1))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def kings_game_safety_wit_33 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) <= ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))) (PreH2 : (j < ((n_pre - 1) - pass))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= pass)) (PreH16 : (pass < (n_pre - 1))) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= ((n_pre - 1) - pass))) (PreH19 : ((Zlength (cur)) = n_pre)) (PreH20 : (FlatMinisters flat_cur cur)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH25 : (MinisterPermutation input cur)) (PreH26 : (BubbleOuterProperty cur n_pre pass)) (PreH27 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def kings_game_safety_wit_34 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j >= ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ ((pass + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pass + 1)) ”

noncomputable def kings_game_entail_wit_1 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.undef_full ans_pre (2 * n_pre))
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (input_flat)) = (2 * n_pre)) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (2 * n_pre)) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) (0 : Int) (sublist ((0 : Int)) ((0 : Int)) (input_flat)))
  ** (intArray.undef_seg ans_pre (0 : Int) (2 * n_pre))
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) ,
  TT && emp 
|--
  “ ((Zlength (input_flat)) = (2 * n_pre)) ” &&
  “ ((sublist ((0 : Int)) ((0 : Int)) (input_flat)) = (@List.nil Int)) ”
  &&  emp
)

noncomputable def kings_game_entail_wit_1_split_goal_1 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) ,
  ((Zlength (input_flat)) = (2 * n_pre))

noncomputable def kings_game_entail_wit_1_split_goal_2 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : (1 <= king_left_pre)) (PreH4 : (king_left_pre <= 10)) (PreH5 : (1 <= king_right_pre)) (PreH6 : (king_right_pre <= 10)) (PreH7 : ((Zlength (input)) = n_pre)) (PreH8 : (FlatMinisters input_flat input)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) ,
  ((sublist ((0 : Int)) ((0 : Int)) (input_flat)) = (@List.nil Int))

noncomputable def kings_game_entail_wit_2 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (k < (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  (intArray.seg ans_pre (0 : Int) (k + 1) ((sublist ((0 : Int)) (k) (input_flat)) ++ ((Znth k input_flat (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ans_pre (k + 1) (2 * n_pre))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (input_flat)) = (2 * n_pre)) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= (2 * n_pre)) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) (k + 1) (sublist ((0 : Int)) ((k + 1)) (input_flat)))
  ** (intArray.undef_seg ans_pre (k + 1) (2 * n_pre))
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (k : Int) (PreH1 : (k < (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  TT && emp 
|--
  “ (((sublist ((0 : Int)) (k) (input_flat)) ++ ((Znth k input_flat (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((k + 1)) (input_flat))) ”
  &&  emp
)

noncomputable def kings_game_entail_wit_2_split_goal_1 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (k : Int) (PreH1 : (k < (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  (((sublist ((0 : Int)) (k) (input_flat)) ++ ((Znth k input_flat (0 : Int)) :: (@List.nil Int))) = (sublist ((0 : Int)) ((k + 1)) (input_flat)))

noncomputable def kings_game_entail_wit_3 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (k >= (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))
  ** (intArray.undef_seg ans_pre k (2 * n_pre))
|--
  EX flat_cur : (List Int), EX cur : (List minister),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre - 1)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre (0 : Int)) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (k : Int) (PreH1 : (k >= (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  TT && emp 
|--
  EX cur : (List minister),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((Zlength (input)) - 1)) ” &&
  “ ((Zlength (cur)) = (Zlength (input))) ” &&
  “ (FlatMinisters (sublist ((0 : Int)) (k) (input_flat)) cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur (Zlength (input)) (0 : Int)) ”
  &&  emp
)

noncomputable def kings_game_entail_wit_4 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (pass : Int) (PreH1 : (pass < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass <= (n_pre - 1))) (PreH16 : ((Zlength (cur_2)) = n_pre)) (PreH17 : (FlatMinisters flat_cur_2 cur_2)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH22 : (MinisterPermutation input cur_2)) (PreH23 : (BubbleOuterProperty cur_2 n_pre pass)) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur_2)
|--
  EX flat_cur : (List Int), EX cur : (List minister),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass (0 : Int)) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (pass : Int) (PreH1 : (pass < (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass <= (n_pre - 1))) (PreH16 : ((Zlength (cur_2)) = n_pre)) (PreH17 : (FlatMinisters flat_cur_2 cur_2)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH22 : (MinisterPermutation input cur_2)) (PreH23 : (BubbleOuterProperty cur_2 n_pre pass)) ,
  TT && emp 
|--
  EX cur : (List minister),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (((Zlength (input)) - 1) - pass)) ” &&
  “ ((Zlength (cur)) = (Zlength (input))) ” &&
  “ (FlatMinisters flat_cur_2 cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur (Zlength (input)) pass) ” &&
  “ (BubbleScanProperty cur (Zlength (input)) pass (0 : Int)) ”
  &&  emp
)

noncomputable def kings_game_entail_wit_5_1 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (PreH1 : (FlatMinisters (minister_swap_flat (flat_cur_2) (j) ((j + 1))) (minister_swap (cur_2) (j) ((j + 1))))) (PreH2 : (MinisterPermutation cur_2 (minister_swap (cur_2) (j) ((j + 1))))) (PreH3 : (((Znth (2 * j) flat_cur_2 (0 : Int)) * (Znth ((2 * j) + 1) flat_cur_2 (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur_2 (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur_2 (0 : Int))))) (PreH4 : (j < ((n_pre - 1) - pass))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : (1 <= king_left_pre)) (PreH8 : (king_left_pre <= 10)) (PreH9 : (1 <= king_right_pre)) (PreH10 : (king_right_pre <= 10)) (PreH11 : ((Zlength (input)) = n_pre)) (PreH12 : (FlatMinisters input_flat input)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH16 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH17 : ((0 : Int) <= pass)) (PreH18 : (pass < (n_pre - 1))) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= ((n_pre - 1) - pass))) (PreH21 : ((Zlength (cur_2)) = n_pre)) (PreH22 : (FlatMinisters flat_cur_2 cur_2)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH26 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH27 : (MinisterPermutation input cur_2)) (PreH28 : (BubbleOuterProperty cur_2 n_pre pass)) (PreH29 : (BubbleScanProperty cur_2 n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) (minister_swap_flat (flat_cur_2) (j) ((j + 1))))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  EX flat_cur : (List Int), EX cur : (List minister),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass (j + 1)) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (j : Int) (pass : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (PreH1 : (FlatMinisters (minister_swap_flat (flat_cur_2) (j) ((j + 1))) (minister_swap (cur_2) (j) ((j + 1))))) (PreH2 : (MinisterPermutation cur_2 (minister_swap (cur_2) (j) ((j + 1))))) (PreH3 : (((Znth (2 * j) flat_cur_2 (0 : Int)) * (Znth ((2 * j) + 1) flat_cur_2 (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur_2 (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur_2 (0 : Int))))) (PreH4 : (j < ((n_pre - 1) - pass))) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : (1 <= king_left_pre)) (PreH8 : (king_left_pre <= 10)) (PreH9 : (1 <= king_right_pre)) (PreH10 : (king_right_pre <= 10)) (PreH11 : ((Zlength (input)) = n_pre)) (PreH12 : (FlatMinisters input_flat input)) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH15 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH16 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH17 : ((0 : Int) <= pass)) (PreH18 : (pass < (n_pre - 1))) (PreH19 : ((0 : Int) <= j)) (PreH20 : (j <= ((n_pre - 1) - pass))) (PreH21 : ((Zlength (cur_2)) = n_pre)) (PreH22 : (FlatMinisters flat_cur_2 cur_2)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH25 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH26 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH27 : (MinisterPermutation input cur_2)) (PreH28 : (BubbleOuterProperty cur_2 n_pre pass)) (PreH29 : (BubbleScanProperty cur_2 n_pre pass j)) ,
  TT && emp 
|--
  EX cur : (List minister),
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (((Zlength (input)) - 1) - pass)) ” &&
  “ ((Zlength (cur)) = (Zlength (input))) ” &&
  “ (FlatMinisters (minister_swap_flat (flat_cur_2) (j) ((j + 1))) cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur (Zlength (input)) pass) ” &&
  “ (BubbleScanProperty cur (Zlength (input)) pass (j + 1)) ”
  &&  emp
)

noncomputable def kings_game_entail_wit_5_2 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (PreH1 : (((Znth (2 * j) flat_cur_2 (0 : Int)) * (Znth ((2 * j) + 1) flat_cur_2 (0 : Int))) <= ((Znth (2 * (j + 1)) flat_cur_2 (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur_2 (0 : Int))))) (PreH2 : (j < ((n_pre - 1) - pass))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= pass)) (PreH16 : (pass < (n_pre - 1))) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= ((n_pre - 1) - pass))) (PreH19 : ((Zlength (cur_2)) = n_pre)) (PreH20 : (FlatMinisters flat_cur_2 cur_2)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH25 : (MinisterPermutation input cur_2)) (PreH26 : (BubbleOuterProperty cur_2 n_pre pass)) (PreH27 : (BubbleScanProperty cur_2 n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur_2)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  EX flat_cur : (List Int), EX cur : (List minister),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass (j + 1)) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (j : Int) (pass : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (PreH1 : (((Znth (2 * j) flat_cur_2 (0 : Int)) * (Znth ((2 * j) + 1) flat_cur_2 (0 : Int))) <= ((Znth (2 * (j + 1)) flat_cur_2 (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur_2 (0 : Int))))) (PreH2 : (j < ((n_pre - 1) - pass))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= pass)) (PreH16 : (pass < (n_pre - 1))) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= ((n_pre - 1) - pass))) (PreH19 : ((Zlength (cur_2)) = n_pre)) (PreH20 : (FlatMinisters flat_cur_2 cur_2)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH25 : (MinisterPermutation input cur_2)) (PreH26 : (BubbleOuterProperty cur_2 n_pre pass)) (PreH27 : (BubbleScanProperty cur_2 n_pre pass j)) ,
  TT && emp 
|--
  EX cur : (List minister),
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (((Zlength (input)) - 1) - pass)) ” &&
  “ ((Zlength (cur)) = (Zlength (input))) ” &&
  “ (FlatMinisters flat_cur_2 cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur (Zlength (input)) pass) ” &&
  “ (BubbleScanProperty cur (Zlength (input)) pass (j + 1)) ”
  &&  emp
)

noncomputable def kings_game_entail_wit_6 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (j : Int) (pass : Int) (PreH1 : (j >= ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur_2)) = n_pre)) (PreH19 : (FlatMinisters flat_cur_2 cur_2)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH24 : (MinisterPermutation input cur_2)) (PreH25 : (BubbleOuterProperty cur_2 n_pre pass)) (PreH26 : (BubbleScanProperty cur_2 n_pre pass j)) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur_2)
|--
  EX flat_cur : (List Int), EX cur : (List minister),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= (pass + 1)) ” &&
  “ ((pass + 1) <= (n_pre - 1)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre (pass + 1)) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (flat_cur_2 : (List Int)) (cur_2 : (List minister)) (j : Int) (pass : Int) (PreH1 : (j >= ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur_2)) = n_pre)) (PreH19 : (FlatMinisters flat_cur_2 cur_2)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur_2)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur_2)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur_2)))) (PreH24 : (MinisterPermutation input cur_2)) (PreH25 : (BubbleOuterProperty cur_2 n_pre pass)) (PreH26 : (BubbleScanProperty cur_2 n_pre pass j)) ,
  TT && emp 
|--
  EX cur : (List minister),
  “ ((0 : Int) <= (pass + 1)) ” &&
  “ ((pass + 1) <= ((Zlength (input)) - 1)) ” &&
  “ ((Zlength (cur)) = (Zlength (input))) ” &&
  “ (FlatMinisters flat_cur_2 cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur (Zlength (input)) (pass + 1)) ”
  &&  emp
)

noncomputable def kings_game_return_wit_1 : Prop :=
  (
forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (pass : Int) (PreH1 : (pass >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass <= (n_pre - 1))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH22 : (MinisterPermutation input cur)) (PreH23 : (BubbleOuterProperty cur n_pre pass)) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  EX output_flat : (List Int), EX output : (List minister),
  “ (FlatMinisters output_flat output) ” &&
  “ (KingsGameResult input king_left_pre output) ”
  &&  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) output_flat)
) \/
(
forall (input : (List minister)) (input_flat : (List Int)) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (pass : Int) (PreH1 : (pass >= (n_pre - 1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass <= (n_pre - 1))) (PreH16 : ((Zlength (cur)) = n_pre)) (PreH17 : (FlatMinisters flat_cur cur)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH22 : (MinisterPermutation input cur)) (PreH23 : (BubbleOuterProperty cur n_pre pass)) ,
  TT && emp 
|--
  EX output : (List minister),
  “ (FlatMinisters flat_cur output) ” &&
  “ (KingsGameResult input king_left_pre output) ”
  &&  emp
)

noncomputable def kings_game_partial_solve_wit_1 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (k < (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))
  ** (intArray.undef_seg ans_pre k (2 * n_pre))
|--
  “ (k < (2 * n_pre)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (input_flat)) = (2 * n_pre)) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= (2 * n_pre)) ”
  &&  (((ministers_pre + (k * sizeof(INT)))) # Int |-> ((Znth k input_flat (0 : Int))))
  ** (intArray.missing_i ministers_pre k (0 : Int) (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))
  ** (intArray.undef_seg ans_pre k (2 * n_pre))

noncomputable def kings_game_partial_solve_wit_2 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (k : Int) (PreH1 : (k < (2 * n_pre))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : ((Zlength (input_flat)) = (2 * n_pre))) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= k)) (PreH16 : (k <= (2 * n_pre))) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))
  ** (intArray.undef_seg ans_pre k (2 * n_pre))
|--
  “ (k < (2 * n_pre)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ ((Zlength (input_flat)) = (2 * n_pre)) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= (2 * n_pre)) ”
  &&  (((ans_pre + (k * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ans_pre (k + 1) (2 * n_pre))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.seg ans_pre (0 : Int) k (sublist ((0 : Int)) (k) (input_flat)))

noncomputable def kings_game_partial_solve_wit_3 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ministers_pre (2 * n_pre) input_flat)
  ** (intArray.full ans_pre (2 * n_pre) flat_cur)
|--
  “ (j < ((n_pre - 1) - pass)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass j) ”
  &&  (((ans_pre + ((2 * j) * sizeof(INT)))) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** (intArray.missing_i ans_pre (2 * j) (0 : Int) (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)

noncomputable def kings_game_partial_solve_wit_4 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (j < ((n_pre - 1) - pass)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass j) ”
  &&  (((ans_pre + (((2 * j) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** (intArray.missing_i ans_pre ((2 * j) + 1) (0 : Int) (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)

noncomputable def kings_game_partial_solve_wit_5 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (j < ((n_pre - 1) - pass)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass j) ”
  &&  (((ans_pre + ((2 * (j + 1)) * sizeof(INT)))) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** (intArray.missing_i ans_pre (2 * (j + 1)) (0 : Int) (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)

noncomputable def kings_game_partial_solve_wit_6 : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (flat_cur : (List Int)) (cur : (List minister)) (j : Int) (pass : Int) (PreH1 : (j < ((n_pre - 1) - pass))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : (1 <= king_left_pre)) (PreH5 : (king_left_pre <= 10)) (PreH6 : (1 <= king_right_pre)) (PreH7 : (king_right_pre <= 10)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (FlatMinisters input_flat input)) (PreH10 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH11 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH13 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH14 : ((0 : Int) <= pass)) (PreH15 : (pass < (n_pre - 1))) (PreH16 : ((0 : Int) <= j)) (PreH17 : (j <= ((n_pre - 1) - pass))) (PreH18 : ((Zlength (cur)) = n_pre)) (PreH19 : (FlatMinisters flat_cur cur)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH23 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH24 : (MinisterPermutation input cur)) (PreH25 : (BubbleOuterProperty cur n_pre pass)) (PreH26 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ (j < ((n_pre - 1) - pass)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass j) ”
  &&  (((ans_pre + (((2 * (j + 1)) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** (intArray.missing_i ans_pre ((2 * (j + 1)) + 1) (0 : Int) (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)

noncomputable def kings_game_partial_solve_wit_7_pure : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))) (PreH2 : (j < ((n_pre - 1) - pass))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= pass)) (PreH16 : (pass < (n_pre - 1))) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= ((n_pre - 1) - pass))) (PreH19 : ((Zlength (cur)) = n_pre)) (PreH20 : (FlatMinisters flat_cur cur)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH25 : (MinisterPermutation input cur)) (PreH26 : (BubbleOuterProperty cur n_pre pass)) (PreH27 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** ((( &( "right2" ) )) # Int |-> ((Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))
  ** ((( &( "left2" ) )) # Int |-> ((Znth (2 * (j + 1)) flat_cur (0 : Int))))
  ** ((( &( "right1" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "left1" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "ministers" ) )) # Ptr |-> (ministers_pre))
  ** ((( &( "ans" ) )) # Ptr |-> (ans_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "king_left" ) )) # Int |-> (king_left_pre))
  ** ((( &( "king_right" ) )) # Int |-> (king_right_pre))
  ** ((( &( "pass" ) )) # Int |-> (pass))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ”

noncomputable def kings_game_partial_solve_wit_7_aux : Prop :=
  forall (input : (List minister)) (input_flat : (List Int)) (ministers_pre : Int) (n_pre : Int) (king_left_pre : Int) (king_right_pre : Int) (ans_pre : Int) (j : Int) (pass : Int) (flat_cur : (List Int)) (cur : (List minister)) (PreH1 : (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int))))) (PreH2 : (j < ((n_pre - 1) - pass))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : (1 <= king_left_pre)) (PreH6 : (king_left_pre <= 10)) (PreH7 : (1 <= king_right_pre)) (PreH8 : (king_right_pre <= 10)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (FlatMinisters input_flat input)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input)))) (PreH13 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input)))) (PreH14 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input)))) (PreH15 : ((0 : Int) <= pass)) (PreH16 : (pass < (n_pre - 1))) (PreH17 : ((0 : Int) <= j)) (PreH18 : (j <= ((n_pre - 1) - pass))) (PreH19 : ((Zlength (cur)) = n_pre)) (PreH20 : (FlatMinisters flat_cur cur)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur)))) (PreH22 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur)))) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur)))) (PreH24 : (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur)))) (PreH25 : (MinisterPermutation input cur)) (PreH26 : (BubbleOuterProperty cur n_pre pass)) (PreH27 : (BubbleScanProperty cur n_pre pass j)) ,
  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)
|--
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (((Znth (2 * j) flat_cur (0 : Int)) * (Znth ((2 * j) + 1) flat_cur (0 : Int))) > ((Znth (2 * (j + 1)) flat_cur (0 : Int)) * (Znth ((2 * (j + 1)) + 1) flat_cur (0 : Int)))) ” &&
  “ (j < ((n_pre - 1) - pass)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ (1 <= king_left_pre) ” &&
  “ (king_left_pre <= 10) ” &&
  “ (1 <= king_right_pre) ” &&
  “ (king_right_pre <= 10) ” &&
  “ ((Zlength (input)) = n_pre) ” &&
  “ (FlatMinisters input_flat input) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (input))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (input))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (input))) ” &&
  “ ((0 : Int) <= pass) ” &&
  “ (pass < (n_pre - 1)) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= ((n_pre - 1) - pass)) ” &&
  “ ((Zlength (cur)) = n_pre) ” &&
  “ (FlatMinisters flat_cur cur) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_left) (cur))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (List.map (minister_right) (cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10)) (List.map (minister_right) (cur))) ” &&
  “ (MinisterPermutation input cur) ” &&
  “ (BubbleOuterProperty cur n_pre pass) ” &&
  “ (BubbleScanProperty cur n_pre pass j) ”
  &&  (intArray.full ans_pre (2 * n_pre) flat_cur)
  ** (intArray.full ministers_pre (2 * n_pre) input_flat)

noncomputable def kings_game_partial_solve_wit_7 : Prop := kings_game_partial_solve_wit_7_pure -> kings_game_partial_solve_wit_7_aux


structure VC_Correct : Type where
  proof_of_swap_ministers_safety_wit_1 : swap_ministers_safety_wit_1
  proof_of_swap_ministers_safety_wit_2 : swap_ministers_safety_wit_2
  proof_of_swap_ministers_safety_wit_3 : swap_ministers_safety_wit_3
  proof_of_swap_ministers_safety_wit_4 : swap_ministers_safety_wit_4
  proof_of_swap_ministers_safety_wit_5 : swap_ministers_safety_wit_5
  proof_of_swap_ministers_safety_wit_6 : swap_ministers_safety_wit_6
  proof_of_swap_ministers_safety_wit_7 : swap_ministers_safety_wit_7
  proof_of_swap_ministers_safety_wit_8 : swap_ministers_safety_wit_8
  proof_of_swap_ministers_safety_wit_9 : swap_ministers_safety_wit_9
  proof_of_swap_ministers_safety_wit_10 : swap_ministers_safety_wit_10
  proof_of_swap_ministers_safety_wit_11 : swap_ministers_safety_wit_11
  proof_of_swap_ministers_safety_wit_12 : swap_ministers_safety_wit_12
  proof_of_swap_ministers_safety_wit_13 : swap_ministers_safety_wit_13
  proof_of_swap_ministers_safety_wit_14 : swap_ministers_safety_wit_14
  proof_of_swap_ministers_safety_wit_15 : swap_ministers_safety_wit_15
  proof_of_swap_ministers_safety_wit_16 : swap_ministers_safety_wit_16
  proof_of_swap_ministers_safety_wit_17 : swap_ministers_safety_wit_17
  proof_of_swap_ministers_safety_wit_18 : swap_ministers_safety_wit_18
  proof_of_swap_ministers_safety_wit_19 : swap_ministers_safety_wit_19
  proof_of_swap_ministers_safety_wit_20 : swap_ministers_safety_wit_20
  proof_of_swap_ministers_safety_wit_21 : swap_ministers_safety_wit_21
  proof_of_swap_ministers_safety_wit_22 : swap_ministers_safety_wit_22
  proof_of_swap_ministers_safety_wit_23 : swap_ministers_safety_wit_23
  proof_of_swap_ministers_safety_wit_24 : swap_ministers_safety_wit_24
  proof_of_swap_ministers_partial_solve_wit_1 : swap_ministers_partial_solve_wit_1
  proof_of_swap_ministers_partial_solve_wit_2 : swap_ministers_partial_solve_wit_2
  proof_of_swap_ministers_partial_solve_wit_3 : swap_ministers_partial_solve_wit_3
  proof_of_swap_ministers_partial_solve_wit_4 : swap_ministers_partial_solve_wit_4
  proof_of_swap_ministers_partial_solve_wit_5 : swap_ministers_partial_solve_wit_5
  proof_of_swap_ministers_partial_solve_wit_6 : swap_ministers_partial_solve_wit_6
  proof_of_swap_ministers_partial_solve_wit_7 : swap_ministers_partial_solve_wit_7
  proof_of_swap_ministers_partial_solve_wit_8 : swap_ministers_partial_solve_wit_8
  proof_of_kings_game_safety_wit_1 : kings_game_safety_wit_1
  proof_of_kings_game_safety_wit_2 : kings_game_safety_wit_2
  proof_of_kings_game_safety_wit_3 : kings_game_safety_wit_3
  proof_of_kings_game_safety_wit_4 : kings_game_safety_wit_4
  proof_of_kings_game_safety_wit_5 : kings_game_safety_wit_5
  proof_of_kings_game_safety_wit_6 : kings_game_safety_wit_6
  proof_of_kings_game_safety_wit_7 : kings_game_safety_wit_7
  proof_of_kings_game_safety_wit_8 : kings_game_safety_wit_8
  proof_of_kings_game_safety_wit_9 : kings_game_safety_wit_9
  proof_of_kings_game_safety_wit_10 : kings_game_safety_wit_10
  proof_of_kings_game_safety_wit_11 : kings_game_safety_wit_11
  proof_of_kings_game_safety_wit_12 : kings_game_safety_wit_12
  proof_of_kings_game_safety_wit_13 : kings_game_safety_wit_13
  proof_of_kings_game_safety_wit_14 : kings_game_safety_wit_14
  proof_of_kings_game_safety_wit_15 : kings_game_safety_wit_15
  proof_of_kings_game_safety_wit_16 : kings_game_safety_wit_16
  proof_of_kings_game_safety_wit_17 : kings_game_safety_wit_17
  proof_of_kings_game_safety_wit_18 : kings_game_safety_wit_18
  proof_of_kings_game_safety_wit_19 : kings_game_safety_wit_19
  proof_of_kings_game_safety_wit_20 : kings_game_safety_wit_20
  proof_of_kings_game_safety_wit_21 : kings_game_safety_wit_21
  proof_of_kings_game_safety_wit_22 : kings_game_safety_wit_22
  proof_of_kings_game_safety_wit_23 : kings_game_safety_wit_23
  proof_of_kings_game_safety_wit_24 : kings_game_safety_wit_24
  proof_of_kings_game_safety_wit_25 : kings_game_safety_wit_25
  proof_of_kings_game_safety_wit_26 : kings_game_safety_wit_26
  proof_of_kings_game_safety_wit_27 : kings_game_safety_wit_27
  proof_of_kings_game_safety_wit_30 : kings_game_safety_wit_30
  proof_of_kings_game_safety_wit_31 : kings_game_safety_wit_31
  proof_of_kings_game_safety_wit_32 : kings_game_safety_wit_32
  proof_of_kings_game_safety_wit_33 : kings_game_safety_wit_33
  proof_of_kings_game_safety_wit_34 : kings_game_safety_wit_34
  proof_of_kings_game_partial_solve_wit_1 : kings_game_partial_solve_wit_1
  proof_of_kings_game_partial_solve_wit_2 : kings_game_partial_solve_wit_2
  proof_of_kings_game_partial_solve_wit_3 : kings_game_partial_solve_wit_3
  proof_of_kings_game_partial_solve_wit_4 : kings_game_partial_solve_wit_4
  proof_of_kings_game_partial_solve_wit_5 : kings_game_partial_solve_wit_5
  proof_of_kings_game_partial_solve_wit_6 : kings_game_partial_solve_wit_6
  proof_of_kings_game_partial_solve_wit_7_pure : kings_game_partial_solve_wit_7_pure
  proof_of_kings_game_partial_solve_wit_7 : kings_game_partial_solve_wit_7
  proof_of_swap_ministers_return_wit_1 : swap_ministers_return_wit_1
  proof_of_kings_game_safety_wit_28 : kings_game_safety_wit_28
  proof_of_kings_game_safety_wit_29 : kings_game_safety_wit_29
  proof_of_kings_game_entail_wit_1 : kings_game_entail_wit_1
  proof_of_kings_game_entail_wit_2 : kings_game_entail_wit_2
  proof_of_kings_game_entail_wit_3 : kings_game_entail_wit_3
  proof_of_kings_game_entail_wit_4 : kings_game_entail_wit_4
  proof_of_kings_game_entail_wit_5_1 : kings_game_entail_wit_5_1
  proof_of_kings_game_entail_wit_5_2 : kings_game_entail_wit_5_2
  proof_of_kings_game_entail_wit_6 : kings_game_entail_wit_6
  proof_of_kings_game_return_wit_1 : kings_game_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.kings_game.kings_game_goal
