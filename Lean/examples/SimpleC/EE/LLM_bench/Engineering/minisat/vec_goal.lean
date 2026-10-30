import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Engineering.minisat.vec_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Engineering.minisat.vec_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance vec_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def veci_new_safety_wit_1 : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |->_)
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |->_)
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def veci_new_safety_wit_2 : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |->_)
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ (4 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 4) ”

noncomputable def veci_new_return_wit_1 : Prop :=
  (
forall (v_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (vec_alloc_ok sizeof(INT) 4)) (PreH3 : (v_pre ≠ (0 : Int))) ,
  (intArray.undef_full retval 4)
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (retval))
|--
  EX buf : Int,
  (veci_raw v_pre buf 4 (@List.nil Int))
) \/
(
forall (v_pre : Int) (retval : Int) (PreH1 : (4 <= INT_MAX)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : (4 >= INT_MIN)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (retval ≠ (0 : Int))) (PreH6 : (vec_alloc_ok sizeof(INT) 4)) (PreH7 : (v_pre ≠ (0 : Int))) ,
  (intArray.undef_full retval 4)
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (retval))
|--
  EX buf : Int,
  (veci_raw v_pre buf 4 (@List.nil Int))
)

noncomputable def veci_new_partial_solve_wit_1 : Prop :=
  forall (v_pre : Int) ,
  (veci_shell v_pre)
|--
  (veci_shell v_pre)

noncomputable def veci_new_partial_solve_wit_2_pure : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ ((0 : Int) <= 4) ” &&
  “ ((4 * sizeof(INT)) <= UINT_MAX) ” &&
  “ ((sizeof(INT) * 4) = (4 * sizeof(INT))) ”

noncomputable def veci_new_partial_solve_wit_2_aux : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ ((0 : Int) <= 4) ” &&
  “ ((4 * sizeof(INT)) <= UINT_MAX) ” &&
  “ ((sizeof(INT) * 4) = (4 * sizeof(INT))) ” &&
  “ (v_pre ≠ (0 : Int)) ”
  &&  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |->_)

noncomputable def veci_new_partial_solve_wit_2 : Prop := veci_new_partial_solve_wit_2_pure -> veci_new_partial_solve_wit_2_aux

noncomputable def veci_new_which_implies_wit_1 : Prop :=
  (
forall (v : Int) ,
  (veci_shell v)
|--
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |->_)
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |->_)
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |->_)
) \/
(
forall (v : Int) ,
  (veci_shell v)
|--
  EX x_3 : Int, EX x_2 : Int, EX x : Int,
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (x_3))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (x_2))
  ** ((&((v # "veci_t")  ->ₛ "size")) # Int |-> (x))
)

noncomputable def veci_delete_return_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
|--
  (veci_shell v_pre)
) \/
(
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
|--
  (veci_shell v_pre)
)

noncomputable def veci_delete_return_wit_1_split_goal_spatial : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
|--
  (veci_shell v_pre)

noncomputable def veci_delete_partial_solve_wit_1 : Prop :=
  forall (xs : (List Int)) (v_pre : Int) ,
  (store_veci v_pre xs)
|--
  (store_veci v_pre xs)

noncomputable def veci_delete_partial_solve_wit_2_pure : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ”

noncomputable def veci_delete_partial_solve_wit_2_aux : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))

noncomputable def veci_delete_partial_solve_wit_2 : Prop := veci_delete_partial_solve_wit_2_pure -> veci_delete_partial_solve_wit_2_aux

noncomputable def veci_delete_which_implies_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v : Int) ,
  (store_veci v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (xs : (List Int)) (v : Int) ,
  (store_veci v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def veci_begin_return_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v_pre : Int) (cap_2 : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap_2)) (PreH5 : (4 <= cap_2)) (PreH6 : (cap_2 <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap_2)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap_2))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap_2)
|--
  EX cap : Int,
  (veci_raw v_pre buf cap xs)
) \/
(
forall (xs : (List Int)) (v_pre : Int) (cap_2 : Int) (buf : Int) (PreH1 : (cap_2 <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap_2 >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap_2)) (PreH9 : (4 <= cap_2)) (PreH10 : (cap_2 <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap_2)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap_2))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap_2)
|--
  EX cap : Int,
  (veci_raw v_pre buf cap xs)
)

noncomputable def veci_begin_partial_solve_wit_1 : Prop :=
  forall (xs : (List Int)) (v_pre : Int) ,
  (store_veci v_pre xs)
|--
  (store_veci v_pre xs)

noncomputable def veci_begin_which_implies_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v : Int) ,
  (store_veci v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (xs : (List Int)) (v : Int) ,
  (store_veci v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def veci_size_return_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((Zlength (xs)) = (Zlength (xs))) ”
  &&  (store_veci v_pre xs)
) \/
(
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  (store_veci v_pre xs)
)

noncomputable def veci_size_return_wit_1_split_goal_spatial : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap)) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  (store_veci v_pre xs)

noncomputable def veci_size_partial_solve_wit_1 : Prop :=
  forall (xs : (List Int)) (v_pre : Int) ,
  (store_veci v_pre xs)
|--
  (store_veci v_pre xs)

noncomputable def veci_size_which_implies_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v : Int) ,
  (store_veci v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (xs : (List Int)) (v : Int) ,
  (store_veci v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def veci_resize_return_wit_1 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(INT) cap)) (PreH8 : ((0 : Int) <= k_pre)) (PreH9 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (k_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  (veci_raw v_pre buf cap (sublist ((0 : Int)) (k_pre) (xs)))
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap)) (PreH12 : ((0 : Int) <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (k_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  (veci_raw v_pre buf cap (sublist ((0 : Int)) (k_pre) (xs)))
)

noncomputable def veci_resize_return_wit_1_split_goal_spatial : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(INT) cap)) (PreH12 : ((0 : Int) <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (k_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  (veci_raw v_pre buf cap (sublist ((0 : Int)) (k_pre) (xs)))

noncomputable def veci_resize_partial_solve_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : ((0 : Int) <= k_pre)) (PreH2 : (k_pre <= (Zlength (xs)))) ,
  (veci_raw v_pre buf cap xs)
|--
  “ ((0 : Int) <= k_pre) ” &&
  “ (k_pre <= (Zlength (xs))) ”
  &&  (veci_raw v_pre buf cap xs)

noncomputable def veci_resize_which_implies_wit_1 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(INT) cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (4 <= cap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def veci_resize_which_implies_wit_1_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(INT) cap) ”

noncomputable def veci_resize_which_implies_wit_1_split_goal_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (cap <= INT_MAX) ”

noncomputable def veci_resize_which_implies_wit_1_split_goal_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (4 <= cap) ”

noncomputable def veci_resize_which_implies_wit_1_split_goal_4 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ ((Zlength (xs)) <= cap) ”

noncomputable def veci_resize_which_implies_wit_1_split_goal_5 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ ((0 : Int) <= (Zlength (xs))) ”

noncomputable def veci_resize_which_implies_wit_1_split_goal_6 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (buf ≠ (0 : Int)) ”

noncomputable def veci_resize_which_implies_wit_1_split_goal_7 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ”

noncomputable def veci_resize_which_implies_wit_1_split_goal_spatial : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)

noncomputable def veci_push_safety_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ (((cap * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((cap * 2) + 1)) ”

noncomputable def veci_push_safety_wit_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ ((cap * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cap * 2)) ”

noncomputable def veci_push_safety_wit_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def veci_push_safety_wit_4 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def veci_push_safety_wit_5 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (intArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (intArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ (((Zlength (xs)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Zlength (xs)) + 1)) ”

noncomputable def veci_push_entail_wit_1_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (vec_alloc_ok sizeof(INT) ((cap * 2) + 1))) (PreH3 : ((Zlength (xs)) = cap)) (PreH4 : (v_pre ≠ (0 : Int))) (PreH5 : (buf ≠ (0 : Int))) (PreH6 : ((0 : Int) <= (Zlength (xs)))) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : (4 <= cap)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (vec_alloc_ok sizeof(INT) cap)) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  (intArray.full retval (Zlength (xs)) xs)
  ** (intArray.undef_seg retval (Zlength (xs)) ((cap * 2) + 1))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (((cap * 2) + 1)))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (retval))
|--
  EX curbuf : Int, EX curcap : Int,
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (intArray.full curbuf (Zlength (xs)) xs)
  ** (intArray.undef_seg curbuf (Zlength (xs)) curcap)

noncomputable def veci_push_entail_wit_1_2 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  EX curbuf : Int, EX curcap : Int,
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (intArray.full curbuf (Zlength (xs)) xs)
  ** (intArray.undef_seg curbuf (Zlength (xs)) curcap)
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  TT && emp 
|--
  “ (((Zlength (xs)) < cap) -> ((buf = buf) ∧ (cap = cap))) ” &&
  “ ((Zlength (xs)) < cap) ”
  &&  emp
)

noncomputable def veci_push_entail_wit_1_2_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  (((Zlength (xs)) < cap) -> ((buf = buf) ∧ (cap = cap)))

noncomputable def veci_push_entail_wit_1_2_split_goal_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((Zlength (xs)) < cap)

noncomputable def veci_push_return_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (curbuf_2 : Int) (curcap_2 : Int) (PreH1 : (vec_push_result (Zlength (xs)) buf cap curbuf_2 curcap_2)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (curbuf ≠ (0 : Int))) (PreH4 : (4 <= curcap)) (PreH5 : (curcap <= INT_MAX)) (PreH6 : (vec_alloc_ok sizeof(INT) curcap)) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : ((Zlength (xs)) < curcap)) (PreH9 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH10 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (veci_raw v_pre curbuf_2 curcap_2 (xs ++ (e_pre :: (@List.nil Int))))
|--
  EX buf2 : Int, EX cap2 : Int,
  “ (vec_push_result (Zlength (xs)) buf cap buf2 cap2) ”
  &&  (veci_raw v_pre buf2 cap2 (xs ++ (e_pre :: (@List.nil Int))))

noncomputable def veci_push_partial_solve_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) <= cap)) (PreH2 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  (veci_raw v_pre buf cap xs)
|--
  “ ((Zlength (xs)) <= cap) ” &&
  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX))) ”
  &&  (veci_raw v_pre buf cap xs)

noncomputable def veci_push_partial_solve_wit_2_pure : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |-> (((cap * 2) + 1)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (cap <= ((cap * 2) + 1)) ” &&
  “ ((((cap * 2) + 1) * sizeof(INT)) <= UINT_MAX) ” &&
  “ ((sizeof(INT) * ((cap * 2) + 1)) = (((cap * 2) + 1) * sizeof(INT))) ” &&
  “ (vec_alloc_ok sizeof(INT) ((cap * 2) + 1)) ”
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (xs)) <= INT_MAX)) (PreH4 : (((cap * 2) + 1) <= INT_MAX)) (PreH5 : (e_pre >= INT_MIN)) (PreH6 : (cap >= INT_MIN)) (PreH7 : ((Zlength (xs)) >= INT_MIN)) (PreH8 : (((cap * 2) + 1) >= INT_MIN)) (PreH9 : ((Zlength (xs)) = cap)) (PreH10 : (v_pre ≠ (0 : Int))) (PreH11 : (buf ≠ (0 : Int))) (PreH12 : ((0 : Int) <= (Zlength (xs)))) (PreH13 : ((Zlength (xs)) <= cap)) (PreH14 : (4 <= cap)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (vec_alloc_ok sizeof(INT) cap)) (PreH17 : ((Zlength (xs)) <= cap)) (PreH18 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |-> (((cap * 2) + 1)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ (vec_alloc_ok sizeof(INT) ((cap * 2) + 1)) ”
)

noncomputable def veci_push_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : (e_pre <= INT_MAX)) (PreH2 : (cap <= INT_MAX)) (PreH3 : ((Zlength (xs)) <= INT_MAX)) (PreH4 : (((cap * 2) + 1) <= INT_MAX)) (PreH5 : (e_pre >= INT_MIN)) (PreH6 : (cap >= INT_MIN)) (PreH7 : ((Zlength (xs)) >= INT_MIN)) (PreH8 : (((cap * 2) + 1) >= INT_MIN)) (PreH9 : ((Zlength (xs)) = cap)) (PreH10 : (v_pre ≠ (0 : Int))) (PreH11 : (buf ≠ (0 : Int))) (PreH12 : ((0 : Int) <= (Zlength (xs)))) (PreH13 : ((Zlength (xs)) <= cap)) (PreH14 : (4 <= cap)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (vec_alloc_ok sizeof(INT) cap)) (PreH17 : ((Zlength (xs)) <= cap)) (PreH18 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |-> (((cap * 2) + 1)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ (vec_alloc_ok sizeof(INT) ((cap * 2) + 1)) ”

noncomputable def veci_push_partial_solve_wit_2_aux : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(INT) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (cap <= ((cap * 2) + 1)) ” &&
  “ ((((cap * 2) + 1) * sizeof(INT)) <= UINT_MAX) ” &&
  “ ((sizeof(INT) * ((cap * 2) + 1)) = (((cap * 2) + 1) * sizeof(INT))) ” &&
  “ (vec_alloc_ok sizeof(INT) ((cap * 2) + 1)) ” &&
  “ ((Zlength (xs)) = cap) ” &&
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(INT) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(INT)) <= UINT_MAX))) ”
  &&  (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))

noncomputable def veci_push_partial_solve_wit_2 : Prop := veci_push_partial_solve_wit_2_pure -> veci_push_partial_solve_wit_2_aux

noncomputable def veci_push_partial_solve_wit_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (intArray.full curbuf (Zlength (xs)) xs)
  ** (intArray.undef_seg curbuf (Zlength (xs)) curcap)
|--
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  (((curbuf + ((Zlength (xs)) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (intArray.full curbuf (Zlength (xs)) xs)

noncomputable def veci_push_partial_solve_wit_4_pure : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (intArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (intArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** ((( &( "e" ) )) # Int |-> (e_pre))
|--
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”

noncomputable def veci_push_partial_solve_wit_4_aux : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (intArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (intArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
|--
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ” &&
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (intArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (intArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)

noncomputable def veci_push_partial_solve_wit_4 : Prop := veci_push_partial_solve_wit_4_pure -> veci_push_partial_solve_wit_4_aux

noncomputable def veci_push_which_implies_wit_1 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(INT) cap) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(INT) cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (4 <= cap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def veci_push_which_implies_wit_1_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(INT) cap) ”

noncomputable def veci_push_which_implies_wit_1_split_goal_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (cap <= INT_MAX) ”

noncomputable def veci_push_which_implies_wit_1_split_goal_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (4 <= cap) ”

noncomputable def veci_push_which_implies_wit_1_split_goal_4 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ ((Zlength (xs)) <= cap) ”

noncomputable def veci_push_which_implies_wit_1_split_goal_5 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ ((0 : Int) <= (Zlength (xs))) ”

noncomputable def veci_push_which_implies_wit_1_split_goal_6 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (buf ≠ (0 : Int)) ”

noncomputable def veci_push_which_implies_wit_1_split_goal_7 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ”

noncomputable def veci_push_which_implies_wit_1_split_goal_spatial : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (veci_raw v buf cap xs)
|--
  ((&((v # "veci_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "veci_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "veci_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (intArray.full buf (Zlength (xs)) xs)
  ** (intArray.undef_seg buf (Zlength (xs)) cap)

noncomputable def veci_push_which_implies_wit_2 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (curcap_2 : Int) (curbuf_2 : Int) (e : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf_2 ≠ (0 : Int))) (PreH3 : (4 <= curcap_2)) (PreH4 : (curcap_2 <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(INT) curcap_2)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap_2)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) ∧ (curcap_2 = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap) + 1)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap_2))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf_2))
  ** (intArray.full curbuf_2 ((Zlength (xs)) + 1) (xs ++ (e :: (@List.nil Int))))
  ** (intArray.undef_seg curbuf_2 ((Zlength (xs)) + 1) curcap_2)
|--
  EX curbuf : Int, EX curcap : Int,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap) ”
  &&  (veci_raw v_pre curbuf curcap (xs ++ (e :: (@List.nil Int))))
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (curcap_2 : Int) (curbuf_2 : Int) (e : Int) (PreH1 : (curcap_2 <= INT_MAX)) (PreH2 : (((Zlength (xs)) + 1) <= INT_MAX)) (PreH3 : (curcap_2 >= INT_MIN)) (PreH4 : (((Zlength (xs)) + 1) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (curbuf_2 ≠ (0 : Int))) (PreH7 : (4 <= curcap_2)) (PreH8 : (curcap_2 <= INT_MAX)) (PreH9 : (vec_alloc_ok sizeof(INT) curcap_2)) (PreH10 : ((Zlength (xs)) <= cap)) (PreH11 : ((Zlength (xs)) < curcap_2)) (PreH12 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) ∧ (curcap_2 = cap)))) (PreH13 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap) + 1)))) ,
  ((&((v_pre # "veci_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "veci_t")  ->ₛ "cap")) # Int |-> (curcap_2))
  ** ((&((v_pre # "veci_t")  ->ₛ "ptr")) # Ptr |-> (curbuf_2))
  ** (intArray.full curbuf_2 ((Zlength (xs)) + 1) (xs ++ (e :: (@List.nil Int))))
  ** (intArray.undef_seg curbuf_2 ((Zlength (xs)) + 1) curcap_2)
|--
  EX curbuf : Int, EX curcap : Int,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap) ”
  &&  (veci_raw v_pre curbuf curcap (xs ++ (e :: (@List.nil Int))))
)

noncomputable def vecp_new_safety_wit_1 : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |->_)
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |->_)
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def vecp_new_safety_wit_2 : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |->_)
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ (4 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 4) ”

noncomputable def vecp_new_return_wit_1 : Prop :=
  (
forall (v_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (vec_alloc_ok sizeof(PTR) 4)) (PreH3 : (v_pre ≠ (0 : Int))) ,
  (ptrArray.undef_full retval 4)
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (retval))
|--
  EX buf : Int,
  (vecp_raw v_pre buf 4 (@List.nil Int))
) \/
(
forall (v_pre : Int) (retval : Int) (PreH1 : (4 <= INT_MAX)) (PreH2 : ((0 : Int) <= INT_MAX)) (PreH3 : (4 >= INT_MIN)) (PreH4 : ((0 : Int) >= INT_MIN)) (PreH5 : (retval ≠ (0 : Int))) (PreH6 : (vec_alloc_ok sizeof(PTR) 4)) (PreH7 : (v_pre ≠ (0 : Int))) ,
  (ptrArray.undef_full retval 4)
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (retval))
|--
  EX buf : Int,
  (vecp_raw v_pre buf 4 (@List.nil Int))
)

noncomputable def vecp_new_partial_solve_wit_1 : Prop :=
  forall (v_pre : Int) ,
  (vecp_shell v_pre)
|--
  (vecp_shell v_pre)

noncomputable def vecp_new_partial_solve_wit_2_pure : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ ((0 : Int) <= 4) ” &&
  “ ((4 * sizeof(PTR)) <= UINT_MAX) ” &&
  “ ((sizeof(PTR) * 4) = (4 * sizeof(PTR))) ”

noncomputable def vecp_new_partial_solve_wit_2_aux : Prop :=
  forall (v_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |->_)
|--
  “ ((0 : Int) <= 4) ” &&
  “ ((4 * sizeof(PTR)) <= UINT_MAX) ” &&
  “ ((sizeof(PTR) * 4) = (4 * sizeof(PTR))) ” &&
  “ (v_pre ≠ (0 : Int)) ”
  &&  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((0 : Int)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (4))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |->_)

noncomputable def vecp_new_partial_solve_wit_2 : Prop := vecp_new_partial_solve_wit_2_pure -> vecp_new_partial_solve_wit_2_aux

noncomputable def vecp_new_which_implies_wit_1 : Prop :=
  (
forall (v : Int) ,
  (vecp_shell v)
|--
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |->_)
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |->_)
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |->_)
) \/
(
forall (v : Int) ,
  (vecp_shell v)
|--
  EX x_3 : Int, EX x_2 : Int, EX x : Int,
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (x_3))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (x_2))
  ** ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> (x))
)

noncomputable def vecp_delete_return_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
|--
  (vecp_shell v_pre)
) \/
(
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
|--
  (vecp_shell v_pre)
)

noncomputable def vecp_delete_return_wit_1_split_goal_spatial : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
|--
  (vecp_shell v_pre)

noncomputable def vecp_delete_partial_solve_wit_1 : Prop :=
  forall (xs : (List Int)) (v_pre : Int) ,
  (store_vecp v_pre xs)
|--
  (store_vecp v_pre xs)

noncomputable def vecp_delete_partial_solve_wit_2_pure : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ”

noncomputable def vecp_delete_partial_solve_wit_2_aux : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))

noncomputable def vecp_delete_partial_solve_wit_2 : Prop := vecp_delete_partial_solve_wit_2_pure -> vecp_delete_partial_solve_wit_2_aux

noncomputable def vecp_delete_which_implies_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v : Int) ,
  (store_vecp v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (xs : (List Int)) (v : Int) ,
  (store_vecp v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def vecp_begin_return_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v_pre : Int) (cap_2 : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap_2)) (PreH5 : (4 <= cap_2)) (PreH6 : (cap_2 <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap_2)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap_2))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap_2)
|--
  EX cap : Int,
  (vecp_raw v_pre buf cap xs)
) \/
(
forall (xs : (List Int)) (v_pre : Int) (cap_2 : Int) (buf : Int) (PreH1 : (cap_2 <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap_2 >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap_2)) (PreH9 : (4 <= cap_2)) (PreH10 : (cap_2 <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap_2)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap_2))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap_2)
|--
  EX cap : Int,
  (vecp_raw v_pre buf cap xs)
)

noncomputable def vecp_begin_partial_solve_wit_1 : Prop :=
  forall (xs : (List Int)) (v_pre : Int) ,
  (store_vecp v_pre xs)
|--
  (store_vecp v_pre xs)

noncomputable def vecp_begin_which_implies_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v : Int) ,
  (store_vecp v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (xs : (List Int)) (v : Int) ,
  (store_vecp v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def vecp_size_return_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((Zlength (xs)) = (Zlength (xs))) ”
  &&  (store_vecp v_pre xs)
) \/
(
forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  (store_vecp v_pre xs)
)

noncomputable def vecp_size_return_wit_1_split_goal_spatial : Prop :=
  forall (xs : (List Int)) (v_pre : Int) (cap : Int) (buf : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : ((Zlength (xs)) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap)) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  (store_vecp v_pre xs)

noncomputable def vecp_size_partial_solve_wit_1 : Prop :=
  forall (xs : (List Int)) (v_pre : Int) ,
  (store_vecp v_pre xs)
|--
  (store_vecp v_pre xs)

noncomputable def vecp_size_which_implies_wit_1 : Prop :=
  (
forall (xs : (List Int)) (v : Int) ,
  (store_vecp v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (xs : (List Int)) (v : Int) ,
  (store_vecp v xs)
|--
  EX cap : Int, EX buf : Int,
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def vecp_resize_return_wit_1 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (buf ≠ (0 : Int))) (PreH3 : ((0 : Int) <= (Zlength (xs)))) (PreH4 : ((Zlength (xs)) <= cap)) (PreH5 : (4 <= cap)) (PreH6 : (cap <= INT_MAX)) (PreH7 : (vec_alloc_ok sizeof(PTR) cap)) (PreH8 : ((0 : Int) <= k_pre)) (PreH9 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (k_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  (vecp_raw v_pre buf cap (sublist ((0 : Int)) (k_pre) (xs)))
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap)) (PreH12 : ((0 : Int) <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (k_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  (vecp_raw v_pre buf cap (sublist ((0 : Int)) (k_pre) (xs)))
)

noncomputable def vecp_resize_return_wit_1_split_goal_spatial : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : (k_pre <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (k_pre >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (buf ≠ (0 : Int))) (PreH7 : ((0 : Int) <= (Zlength (xs)))) (PreH8 : ((Zlength (xs)) <= cap)) (PreH9 : (4 <= cap)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (vec_alloc_ok sizeof(PTR) cap)) (PreH12 : ((0 : Int) <= k_pre)) (PreH13 : (k_pre <= (Zlength (xs)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (k_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  (vecp_raw v_pre buf cap (sublist ((0 : Int)) (k_pre) (xs)))

noncomputable def vecp_resize_partial_solve_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (k_pre : Int) (PreH1 : ((0 : Int) <= k_pre)) (PreH2 : (k_pre <= (Zlength (xs)))) ,
  (vecp_raw v_pre buf cap xs)
|--
  “ ((0 : Int) <= k_pre) ” &&
  “ (k_pre <= (Zlength (xs))) ”
  &&  (vecp_raw v_pre buf cap xs)

noncomputable def vecp_resize_which_implies_wit_1 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(PTR) cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (4 <= cap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def vecp_resize_which_implies_wit_1_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(PTR) cap) ”

noncomputable def vecp_resize_which_implies_wit_1_split_goal_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (cap <= INT_MAX) ”

noncomputable def vecp_resize_which_implies_wit_1_split_goal_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (4 <= cap) ”

noncomputable def vecp_resize_which_implies_wit_1_split_goal_4 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ ((Zlength (xs)) <= cap) ”

noncomputable def vecp_resize_which_implies_wit_1_split_goal_5 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ ((0 : Int) <= (Zlength (xs))) ”

noncomputable def vecp_resize_which_implies_wit_1_split_goal_6 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (buf ≠ (0 : Int)) ”

noncomputable def vecp_resize_which_implies_wit_1_split_goal_7 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ”

noncomputable def vecp_resize_which_implies_wit_1_split_goal_spatial : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)

noncomputable def vecp_push_safety_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ (((cap * 2) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((cap * 2) + 1)) ”

noncomputable def vecp_push_safety_wit_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ ((cap * 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cap * 2)) ”

noncomputable def vecp_push_safety_wit_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def vecp_push_safety_wit_4 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def vecp_push_safety_wit_5 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (ptrArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (ptrArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ (((Zlength (xs)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Zlength (xs)) + 1)) ”

noncomputable def vecp_push_entail_wit_1_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (vec_alloc_ok sizeof(PTR) ((cap * 2) + 1))) (PreH3 : ((Zlength (xs)) = cap)) (PreH4 : (v_pre ≠ (0 : Int))) (PreH5 : (buf ≠ (0 : Int))) (PreH6 : ((0 : Int) <= (Zlength (xs)))) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : (4 <= cap)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (vec_alloc_ok sizeof(PTR) cap)) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  (ptrArray.full retval (Zlength (xs)) xs)
  ** (ptrArray.undef_seg retval (Zlength (xs)) ((cap * 2) + 1))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (((cap * 2) + 1)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (retval))
|--
  EX curbuf : Int, EX curcap : Int,
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (ptrArray.full curbuf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg curbuf (Zlength (xs)) curcap)

noncomputable def vecp_push_entail_wit_1_2 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  EX curbuf : Int, EX curcap : Int,
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (ptrArray.full curbuf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg curbuf (Zlength (xs)) curcap)
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  TT && emp 
|--
  “ (((Zlength (xs)) < cap) -> ((buf = buf) ∧ (cap = cap))) ” &&
  “ ((Zlength (xs)) < cap) ”
  &&  emp
)

noncomputable def vecp_push_entail_wit_1_2_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  (((Zlength (xs)) < cap) -> ((buf = buf) ∧ (cap = cap)))

noncomputable def vecp_push_entail_wit_1_2_split_goal_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) ≠ cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((Zlength (xs)) < cap)

noncomputable def vecp_push_return_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (curbuf_2 : Int) (curcap_2 : Int) (PreH1 : (vec_push_result (Zlength (xs)) buf cap curbuf_2 curcap_2)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (curbuf ≠ (0 : Int))) (PreH4 : (4 <= curcap)) (PreH5 : (curcap <= INT_MAX)) (PreH6 : (vec_alloc_ok sizeof(PTR) curcap)) (PreH7 : ((Zlength (xs)) <= cap)) (PreH8 : ((Zlength (xs)) < curcap)) (PreH9 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH10 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (vecp_raw v_pre curbuf_2 curcap_2 (xs ++ (e_pre :: (@List.nil Int))))
|--
  EX buf2 : Int, EX cap2 : Int,
  “ (vec_push_result (Zlength (xs)) buf cap buf2 cap2) ”
  &&  (vecp_raw v_pre buf2 cap2 (xs ++ (e_pre :: (@List.nil Int))))

noncomputable def vecp_push_partial_solve_wit_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) <= cap)) (PreH2 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  (vecp_raw v_pre buf cap xs)
|--
  “ ((Zlength (xs)) <= cap) ” &&
  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX))) ”
  &&  (vecp_raw v_pre buf cap xs)

noncomputable def vecp_push_partial_solve_wit_2_pure : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |-> (((cap * 2) + 1)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (cap <= ((cap * 2) + 1)) ” &&
  “ ((((cap * 2) + 1) * sizeof(PTR)) <= UINT_MAX) ” &&
  “ ((sizeof(PTR) * ((cap * 2) + 1)) = (((cap * 2) + 1) * sizeof(PTR))) ” &&
  “ (vec_alloc_ok sizeof(PTR) ((cap * 2) + 1)) ”
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (((cap * 2) + 1) <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (xs)) >= INT_MIN)) (PreH6 : (((cap * 2) + 1) >= INT_MIN)) (PreH7 : ((Zlength (xs)) = cap)) (PreH8 : (v_pre ≠ (0 : Int))) (PreH9 : (buf ≠ (0 : Int))) (PreH10 : ((0 : Int) <= (Zlength (xs)))) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (4 <= cap)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (vec_alloc_ok sizeof(PTR) cap)) (PreH15 : ((Zlength (xs)) <= cap)) (PreH16 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |-> (((cap * 2) + 1)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ (vec_alloc_ok sizeof(PTR) ((cap * 2) + 1)) ”
)

noncomputable def vecp_push_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (PreH1 : (cap <= INT_MAX)) (PreH2 : ((Zlength (xs)) <= INT_MAX)) (PreH3 : (((cap * 2) + 1) <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((Zlength (xs)) >= INT_MIN)) (PreH6 : (((cap * 2) + 1) >= INT_MIN)) (PreH7 : ((Zlength (xs)) = cap)) (PreH8 : (v_pre ≠ (0 : Int))) (PreH9 : (buf ≠ (0 : Int))) (PreH10 : ((0 : Int) <= (Zlength (xs)))) (PreH11 : ((Zlength (xs)) <= cap)) (PreH12 : (4 <= cap)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (vec_alloc_ok sizeof(PTR) cap)) (PreH15 : ((Zlength (xs)) <= cap)) (PreH16 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((( &( "newsize" ) )) # Int |-> (((cap * 2) + 1)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ (vec_alloc_ok sizeof(PTR) ((cap * 2) + 1)) ”

noncomputable def vecp_push_partial_solve_wit_2_aux : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (PreH1 : ((Zlength (xs)) = cap)) (PreH2 : (v_pre ≠ (0 : Int))) (PreH3 : (buf ≠ (0 : Int))) (PreH4 : ((0 : Int) <= (Zlength (xs)))) (PreH5 : ((Zlength (xs)) <= cap)) (PreH6 : (4 <= cap)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (vec_alloc_ok sizeof(PTR) cap)) (PreH9 : ((Zlength (xs)) <= cap)) (PreH10 : (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
|--
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (cap <= ((cap * 2) + 1)) ” &&
  “ ((((cap * 2) + 1) * sizeof(PTR)) <= UINT_MAX) ” &&
  “ ((sizeof(PTR) * ((cap * 2) + 1)) = (((cap * 2) + 1) * sizeof(PTR))) ” &&
  “ (vec_alloc_ok sizeof(PTR) ((cap * 2) + 1)) ” &&
  “ ((Zlength (xs)) = cap) ” &&
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (((Zlength (xs)) = cap) -> (((vec_growth_ok sizeof(PTR) cap) ∧ (cap <= 1073741823)) ∧ ((((2 * cap) + 1) * sizeof(PTR)) <= UINT_MAX))) ”
  &&  (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))

noncomputable def vecp_push_partial_solve_wit_2 : Prop := vecp_push_partial_solve_wit_2_pure -> vecp_push_partial_solve_wit_2_aux

noncomputable def vecp_push_partial_solve_wit_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (ptrArray.full curbuf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg curbuf (Zlength (xs)) curcap)
|--
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  (((curbuf + ((Zlength (xs)) * sizeof(PTR)))) # Ptr |->_)
  ** (ptrArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (ptrArray.full curbuf (Zlength (xs)) xs)

noncomputable def vecp_push_partial_solve_wit_4_pure : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (ptrArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (ptrArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** ((( &( "e" ) )) # Ptr |-> (e_pre))
|--
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”

noncomputable def vecp_push_partial_solve_wit_4_aux : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (e_pre : Int) (curbuf : Int) (curcap : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf ≠ (0 : Int))) (PreH3 : (4 <= curcap)) (PreH4 : (curcap <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1)))) ,
  (ptrArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (ptrArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)
  ** ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
|--
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ” &&
  “ (v_pre ≠ (0 : Int)) ” &&
  “ (curbuf ≠ (0 : Int)) ” &&
  “ (4 <= curcap) ” &&
  “ (curcap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) curcap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((Zlength (xs)) < curcap) ” &&
  “ (((Zlength (xs)) < cap) -> ((curbuf = buf) ∧ (curcap = cap))) ” &&
  “ (((Zlength (xs)) = cap) -> (curcap = ((2 * cap) + 1))) ”
  &&  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf))
  ** (ptrArray.full curbuf ((Zlength (xs)) + 1) (xs ++ (e_pre :: (@List.nil Int))))
  ** (ptrArray.undef_seg curbuf ((Zlength (xs)) + 1) curcap)

noncomputable def vecp_push_partial_solve_wit_4 : Prop := vecp_push_partial_solve_wit_4_pure -> vecp_push_partial_solve_wit_4_aux

noncomputable def vecp_push_which_implies_wit_1 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ (4 <= cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (vec_alloc_ok sizeof(PTR) cap) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(PTR) cap) ” &&
  “ (cap <= INT_MAX) ” &&
  “ (4 <= cap) ” &&
  “ ((Zlength (xs)) <= cap) ” &&
  “ ((0 : Int) <= (Zlength (xs))) ” &&
  “ (buf ≠ (0 : Int)) ” &&
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)
)

noncomputable def vecp_push_which_implies_wit_1_split_goal_1 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (vec_alloc_ok sizeof(PTR) cap) ”

noncomputable def vecp_push_which_implies_wit_1_split_goal_2 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (cap <= INT_MAX) ”

noncomputable def vecp_push_which_implies_wit_1_split_goal_3 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (4 <= cap) ”

noncomputable def vecp_push_which_implies_wit_1_split_goal_4 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ ((Zlength (xs)) <= cap) ”

noncomputable def vecp_push_which_implies_wit_1_split_goal_5 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ ((0 : Int) <= (Zlength (xs))) ”

noncomputable def vecp_push_which_implies_wit_1_split_goal_6 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (buf ≠ (0 : Int)) ”

noncomputable def vecp_push_which_implies_wit_1_split_goal_7 : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  “ (v ≠ (0 : Int)) ”

noncomputable def vecp_push_which_implies_wit_1_split_goal_spatial : Prop :=
  forall (cap : Int) (buf : Int) (xs : (List Int)) (v : Int) ,
  (vecp_raw v buf cap xs)
|--
  ((&((v # "vecp_t")  ->ₛ "size")) # Int |-> ((Zlength (xs))))
  ** ((&((v # "vecp_t")  ->ₛ "cap")) # Int |-> (cap))
  ** ((&((v # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (buf))
  ** (ptrArray.full buf (Zlength (xs)) xs)
  ** (ptrArray.undef_seg buf (Zlength (xs)) cap)

noncomputable def vecp_push_which_implies_wit_2 : Prop :=
  (
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (curcap_2 : Int) (curbuf_2 : Int) (e : Int) (PreH1 : (v_pre ≠ (0 : Int))) (PreH2 : (curbuf_2 ≠ (0 : Int))) (PreH3 : (4 <= curcap_2)) (PreH4 : (curcap_2 <= INT_MAX)) (PreH5 : (vec_alloc_ok sizeof(PTR) curcap_2)) (PreH6 : ((Zlength (xs)) <= cap)) (PreH7 : ((Zlength (xs)) < curcap_2)) (PreH8 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) ∧ (curcap_2 = cap)))) (PreH9 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap) + 1)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap_2))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf_2))
  ** (ptrArray.full curbuf_2 ((Zlength (xs)) + 1) (xs ++ (e :: (@List.nil Int))))
  ** (ptrArray.undef_seg curbuf_2 ((Zlength (xs)) + 1) curcap_2)
|--
  EX curbuf : Int, EX curcap : Int,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap) ”
  &&  (vecp_raw v_pre curbuf curcap (xs ++ (e :: (@List.nil Int))))
) \/
(
forall (cap : Int) (buf : Int) (xs : (List Int)) (v_pre : Int) (curcap_2 : Int) (curbuf_2 : Int) (e : Int) (PreH1 : (curcap_2 <= INT_MAX)) (PreH2 : (((Zlength (xs)) + 1) <= INT_MAX)) (PreH3 : (curcap_2 >= INT_MIN)) (PreH4 : (((Zlength (xs)) + 1) >= INT_MIN)) (PreH5 : (v_pre ≠ (0 : Int))) (PreH6 : (curbuf_2 ≠ (0 : Int))) (PreH7 : (4 <= curcap_2)) (PreH8 : (curcap_2 <= INT_MAX)) (PreH9 : (vec_alloc_ok sizeof(PTR) curcap_2)) (PreH10 : ((Zlength (xs)) <= cap)) (PreH11 : ((Zlength (xs)) < curcap_2)) (PreH12 : (((Zlength (xs)) < cap) -> ((curbuf_2 = buf) ∧ (curcap_2 = cap)))) (PreH13 : (((Zlength (xs)) = cap) -> (curcap_2 = ((2 * cap) + 1)))) ,
  ((&((v_pre # "vecp_t")  ->ₛ "size")) # Int |-> (((Zlength (xs)) + 1)))
  ** ((&((v_pre # "vecp_t")  ->ₛ "cap")) # Int |-> (curcap_2))
  ** ((&((v_pre # "vecp_t")  ->ₛ "ptr")) # Ptr |-> (curbuf_2))
  ** (ptrArray.full curbuf_2 ((Zlength (xs)) + 1) (xs ++ (e :: (@List.nil Int))))
  ** (ptrArray.undef_seg curbuf_2 ((Zlength (xs)) + 1) curcap_2)
|--
  EX curbuf : Int, EX curcap : Int,
  “ (vec_push_result (Zlength (xs)) buf cap curbuf curcap) ”
  &&  (vecp_raw v_pre curbuf curcap (xs ++ (e :: (@List.nil Int))))
)


structure VC_Correct : Type where
  proof_of_veci_new_safety_wit_1 : veci_new_safety_wit_1
  proof_of_veci_new_safety_wit_2 : veci_new_safety_wit_2
  proof_of_veci_new_partial_solve_wit_1 : veci_new_partial_solve_wit_1
  proof_of_veci_new_partial_solve_wit_2_pure : veci_new_partial_solve_wit_2_pure
  proof_of_veci_new_partial_solve_wit_2 : veci_new_partial_solve_wit_2
  proof_of_veci_delete_partial_solve_wit_1 : veci_delete_partial_solve_wit_1
  proof_of_veci_delete_partial_solve_wit_2_pure : veci_delete_partial_solve_wit_2_pure
  proof_of_veci_delete_partial_solve_wit_2 : veci_delete_partial_solve_wit_2
  proof_of_veci_begin_partial_solve_wit_1 : veci_begin_partial_solve_wit_1
  proof_of_veci_size_partial_solve_wit_1 : veci_size_partial_solve_wit_1
  proof_of_veci_resize_partial_solve_wit_1 : veci_resize_partial_solve_wit_1
  proof_of_veci_push_safety_wit_1 : veci_push_safety_wit_1
  proof_of_veci_push_safety_wit_2 : veci_push_safety_wit_2
  proof_of_veci_push_safety_wit_3 : veci_push_safety_wit_3
  proof_of_veci_push_safety_wit_4 : veci_push_safety_wit_4
  proof_of_veci_push_safety_wit_5 : veci_push_safety_wit_5
  proof_of_veci_push_entail_wit_1_1 : veci_push_entail_wit_1_1
  proof_of_veci_push_return_wit_1 : veci_push_return_wit_1
  proof_of_veci_push_partial_solve_wit_1 : veci_push_partial_solve_wit_1
  proof_of_veci_push_partial_solve_wit_2 : veci_push_partial_solve_wit_2
  proof_of_veci_push_partial_solve_wit_3 : veci_push_partial_solve_wit_3
  proof_of_veci_push_partial_solve_wit_4_pure : veci_push_partial_solve_wit_4_pure
  proof_of_veci_push_partial_solve_wit_4 : veci_push_partial_solve_wit_4
  proof_of_vecp_new_safety_wit_1 : vecp_new_safety_wit_1
  proof_of_vecp_new_safety_wit_2 : vecp_new_safety_wit_2
  proof_of_vecp_new_partial_solve_wit_1 : vecp_new_partial_solve_wit_1
  proof_of_vecp_new_partial_solve_wit_2_pure : vecp_new_partial_solve_wit_2_pure
  proof_of_vecp_new_partial_solve_wit_2 : vecp_new_partial_solve_wit_2
  proof_of_vecp_delete_partial_solve_wit_1 : vecp_delete_partial_solve_wit_1
  proof_of_vecp_delete_partial_solve_wit_2_pure : vecp_delete_partial_solve_wit_2_pure
  proof_of_vecp_delete_partial_solve_wit_2 : vecp_delete_partial_solve_wit_2
  proof_of_vecp_begin_partial_solve_wit_1 : vecp_begin_partial_solve_wit_1
  proof_of_vecp_size_partial_solve_wit_1 : vecp_size_partial_solve_wit_1
  proof_of_vecp_resize_partial_solve_wit_1 : vecp_resize_partial_solve_wit_1
  proof_of_vecp_push_safety_wit_1 : vecp_push_safety_wit_1
  proof_of_vecp_push_safety_wit_2 : vecp_push_safety_wit_2
  proof_of_vecp_push_safety_wit_3 : vecp_push_safety_wit_3
  proof_of_vecp_push_safety_wit_4 : vecp_push_safety_wit_4
  proof_of_vecp_push_safety_wit_5 : vecp_push_safety_wit_5
  proof_of_vecp_push_entail_wit_1_1 : vecp_push_entail_wit_1_1
  proof_of_vecp_push_return_wit_1 : vecp_push_return_wit_1
  proof_of_vecp_push_partial_solve_wit_1 : vecp_push_partial_solve_wit_1
  proof_of_vecp_push_partial_solve_wit_2 : vecp_push_partial_solve_wit_2
  proof_of_vecp_push_partial_solve_wit_3 : vecp_push_partial_solve_wit_3
  proof_of_vecp_push_partial_solve_wit_4_pure : vecp_push_partial_solve_wit_4_pure
  proof_of_vecp_push_partial_solve_wit_4 : vecp_push_partial_solve_wit_4
  proof_of_veci_new_return_wit_1 : veci_new_return_wit_1
  proof_of_veci_new_which_implies_wit_1 : veci_new_which_implies_wit_1
  proof_of_veci_delete_return_wit_1 : veci_delete_return_wit_1
  proof_of_veci_delete_which_implies_wit_1 : veci_delete_which_implies_wit_1
  proof_of_veci_begin_return_wit_1 : veci_begin_return_wit_1
  proof_of_veci_begin_which_implies_wit_1 : veci_begin_which_implies_wit_1
  proof_of_veci_size_return_wit_1 : veci_size_return_wit_1
  proof_of_veci_size_which_implies_wit_1 : veci_size_which_implies_wit_1
  proof_of_veci_resize_return_wit_1 : veci_resize_return_wit_1
  proof_of_veci_resize_which_implies_wit_1 : veci_resize_which_implies_wit_1
  proof_of_veci_push_entail_wit_1_2 : veci_push_entail_wit_1_2
  proof_of_veci_push_partial_solve_wit_2_pure : veci_push_partial_solve_wit_2_pure
  proof_of_veci_push_which_implies_wit_1 : veci_push_which_implies_wit_1
  proof_of_veci_push_which_implies_wit_2 : veci_push_which_implies_wit_2
  proof_of_vecp_new_return_wit_1 : vecp_new_return_wit_1
  proof_of_vecp_new_which_implies_wit_1 : vecp_new_which_implies_wit_1
  proof_of_vecp_delete_return_wit_1 : vecp_delete_return_wit_1
  proof_of_vecp_delete_which_implies_wit_1 : vecp_delete_which_implies_wit_1
  proof_of_vecp_begin_return_wit_1 : vecp_begin_return_wit_1
  proof_of_vecp_begin_which_implies_wit_1 : vecp_begin_which_implies_wit_1
  proof_of_vecp_size_return_wit_1 : vecp_size_return_wit_1
  proof_of_vecp_size_which_implies_wit_1 : vecp_size_which_implies_wit_1
  proof_of_vecp_resize_return_wit_1 : vecp_resize_return_wit_1
  proof_of_vecp_resize_which_implies_wit_1 : vecp_resize_which_implies_wit_1
  proof_of_vecp_push_entail_wit_1_2 : vecp_push_entail_wit_1_2
  proof_of_vecp_push_partial_solve_wit_2_pure : vecp_push_partial_solve_wit_2_pure
  proof_of_vecp_push_which_implies_wit_1 : vecp_push_which_implies_wit_1
  proof_of_vecp_push_which_implies_wit_2 : vecp_push_which_implies_wit_2

end SimpleC.EE.LLM_bench.Engineering.minisat.vec_goal
