import SimpleC.SL.ArrayLibCore

namespace SimpleC.SL.ArrayLib

open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CNotation
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

structure ArrayLibSig
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    extends ArrayLibCoreSig CRules DePredSig SLibSig where

namespace ArrayLibSig

def canonical (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayLibSig CRules DePredSig SLibSig :=
  ⟨ArrayLibCoreSig.canonical CRules DePredSig SLibSig⟩

private def mkElementStore
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (stride size : Int) (hsize : size = stride)
    (store : SimpleC.SL.Mem.addr -> Int -> CRules.expr)
    (undefstore : SimpleC.SL.Mem.addr -> CRules.expr)
    (hforget : forall p a, CRules.derivable1 (store p a) (undefstore p))
    (hstoreAlign : forall p a,
      CRules.derivable1 (store p a) (store_align_n CRules size))
    (hundefAlign : forall p,
      CRules.derivable1 (undefstore p) (store_align_n CRules size))
    (hvalid : 0 < size ∧ size < Int.max_unsigned) :
    ELEMENT_STORE CRules DePredSig SLibSig where
  A := Int
  sizeA := size
  storeA := fun x lo a => store (x + lo * stride) a
  undefstoreA := fun x lo => undefstore (x + lo * stride)
  store_to_undefstore := by
    intro x lo a
    exact hforget (x + lo * stride) a
  storeA_shift := by
    intro x n lo a
    rw [hsize]
    have haddr : x + n * stride + lo * stride =
        x + (lo + n) * stride := by
      calc
        x + n * stride + lo * stride =
            x + (n * stride + lo * stride) := Int.add_assoc _ _ _
        _ = x + (lo * stride + n * stride) :=
          congrArg (fun z : Int => x + z)
            (Int.add_comm (n * stride) (lo * stride))
        _ = x + (lo + n) * stride := by rw [Int.add_mul]
    rw [haddr]
    exact CRules.toContext.logic_equiv_refl _
  undefstoreA_shift := by
    intro x n lo
    rw [hsize]
    have haddr : x + n * stride + lo * stride =
        x + (lo + n) * stride := by
      calc
        x + n * stride + lo * stride =
            x + (n * stride + lo * stride) := Int.add_assoc _ _ _
        _ = x + (lo * stride + n * stride) :=
          congrArg (fun z : Int => x + z)
            (Int.add_comm (n * stride) (lo * stride))
        _ = x + (lo + n) * stride := by rw [Int.add_mul]
    rw [haddr]
    exact CRules.toContext.logic_equiv_refl _
  store_to_align := by
    intro x lo a
    exact hstoreAlign (x + lo * stride) a
  undefstore_to_align := by
    intro x lo
    exact hundefAlign (x + lo * stride)
  sizeA_valid := hvalid

private theorem store_align4_as_align
    (CRules : SeparationLogicSig) (p a size blocks : Int)
    (hsize : size = 4 * blocks)
    (hstore : CRules.derivable1 (store_int CRules p a)
      (store_align4_n CRules blocks)) :
    CRules.derivable1 (store_int CRules p a) (store_align_n CRules size) := by
  have h := CRules.toContext.derivable1_trans _ _ _ hstore
    (store_align4_to_store_align CRules blocks)
  rw [hsize]
  exact h

private theorem undef_align4_as_align
    (CRules : SeparationLogicSig) (P : CRules.expr) (size blocks : Int)
    (hsize : size = 4 * blocks)
    (hstore : CRules.derivable1 P (store_align4_n CRules blocks)) :
    CRules.derivable1 P (store_align_n CRules size) := by
  have h := CRules.toContext.derivable1_trans _ _ _ hstore
    (store_align4_to_store_align CRules blocks)
  rw [hsize]
  exact h

noncomputable def StoreCharAsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_char) (sizeof_front_end_type FET_char) rfl
    (store_char CRules) (undef_store_char CRules)
    (store_char_undef_store_char CRules)
    (by intro p a; simpa [sizeof_char] using store_char_align CRules p a)
    (by intro p; simpa [sizeof_char] using undef_store_char_align CRules p)
    (by rw [sizeof_char]; constructor <;> decide)

noncomputable def StoreUCharAsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_uchar) (sizeof_front_end_type FET_uchar) rfl
    (store_uchar CRules) (undef_store_uchar CRules)
    (store_uchar_undef_store_uchar CRules)
    (by intro p a; simpa [sizeof_uchar] using store_uchar_align CRules p a)
    (by intro p; simpa [sizeof_uchar] using undef_store_uchar_align CRules p)
    (by rw [sizeof_uchar]; constructor <;> decide)

noncomputable def StoreShortAsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_short) (sizeof_front_end_type FET_short) rfl
    (store_short CRules) (undef_store_short CRules)
    (store_short_undef_store_short CRules)
    (by intro p a; simpa [sizeof_short] using store_short_align CRules p a)
    (by intro p; simpa [sizeof_short] using undef_store_short_align CRules p)
    (by rw [sizeof_short]; constructor <;> decide)

noncomputable def StoreUShortAsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_ushort) (sizeof_front_end_type FET_ushort) rfl
    (store_ushort CRules) (undef_store_ushort CRules)
    (store_ushort_undef_store_ushort CRules)
    (by intro p a; simpa [sizeof_ushort] using store_ushort_align CRules p a)
    (by intro p; simpa [sizeof_ushort] using undef_store_ushort_align CRules p)
    (by rw [sizeof_ushort]; constructor <;> decide)

noncomputable def StoreIntAsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_int) (sizeof_front_end_type FET_int) rfl
    (store_int CRules) (undef_store_int CRules)
    (store_int_undef_store_int CRules)
    (by
      intro p a
      apply undef_align4_as_align CRules (store_int CRules p a) _ 1
      · rw [sizeof_int]; decide
      · exact store_int_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align CRules (undef_store_int CRules p) _ 1
      · rw [sizeof_int]; decide
      · exact undef_store_int_align4 CRules p)
    (by rw [sizeof_int]; constructor <;> decide)

noncomputable def StoreUIntAsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_uint) (sizeof_front_end_type FET_uint) rfl
    (store_uint CRules) (undef_store_uint CRules)
    (store_uint_undef_store_uint CRules)
    (by
      intro p a
      apply undef_align4_as_align CRules (store_uint CRules p a) _ 1
      · rw [sizeof_uint]; decide
      · exact store_uint_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align CRules (undef_store_uint CRules p) _ 1
      · rw [sizeof_uint]; decide
      · exact undef_store_uint_align4 CRules p)
    (by rw [sizeof_uint]; constructor <;> decide)

noncomputable def StoreInt64AsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_int64) (sizeof_front_end_type FET_int64) rfl
    (store_int64 CRules) (undef_store_int64 CRules)
    (store_int64_undef_store_int64 CRules)
    (by
      intro p a
      apply undef_align4_as_align CRules (store_int64 CRules p a) _ 2
      · rw [sizeof_int64]; decide
      · exact store_int64_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align CRules (undef_store_int64 CRules p) _ 2
      · rw [sizeof_int64]; decide
      · exact undef_store_int64_align4 CRules p)
    (by rw [sizeof_int64]; constructor <;> decide)

noncomputable def StoreUInt64AsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    (sizeof_front_end_type FET_uint64) (sizeof_front_end_type FET_uint64) rfl
    (store_uint64 CRules) (undef_store_uint64 CRules)
    (store_uint64_undef_store_uint64 CRules)
    (by
      intro p a
      apply undef_align4_as_align CRules (store_uint64 CRules p a) _ 2
      · rw [sizeof_uint64]; decide
      · exact store_uint64_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align CRules (undef_store_uint64 CRules p) _ 2
      · rw [sizeof_uint64]; decide
      · exact undef_store_uint64_align4 CRules p)
    (by rw [sizeof_uint64]; constructor <;> decide)

noncomputable def StorePtrAsElement (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ELEMENT_STORE CRules DePredSig SLibSig :=
  mkElementStore CRules DePredSig SLibSig
    4 (sizeof_front_end_type FET_ptr) sizeof_ptr
    (store_ptr CRules) (undef_store_ptr CRules)
    (store_ptr_undef_store_ptr CRules)
    (by
      intro p a
      apply undef_align4_as_align CRules (store_ptr CRules p a) _ 1
      · rw [sizeof_ptr]; decide
      · exact store_ptr_align4 CRules p a)
    (by
      intro p
      apply undef_align4_as_align CRules (undef_store_ptr CRules p) _ 1
      · rw [sizeof_ptr]; decide
      · exact undef_store_ptr_align4 CRules p)
    (by rw [sizeof_ptr]; constructor <;> decide)

structure ArrayFacade (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) where
  elementStore : ELEMENT_STORE CRules DePredSig SLibSig

noncomputable def CharArray (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreCharAsElement CRules DePredSig SLibSig⟩

noncomputable def UCharArray (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreUCharAsElement CRules DePredSig SLibSig⟩

noncomputable def ShortArray (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreShortAsElement CRules DePredSig SLibSig⟩

noncomputable def UShortArray (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreUShortAsElement CRules DePredSig SLibSig⟩

noncomputable def IntArray (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreIntAsElement CRules DePredSig SLibSig⟩

noncomputable def UIntArray (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreUIntAsElement CRules DePredSig SLibSig⟩

noncomputable def Int64Array (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreInt64AsElement CRules DePredSig SLibSig⟩

noncomputable def UInt64Array (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StoreUInt64AsElement CRules DePredSig SLibSig⟩

noncomputable def PtrArray (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig) :
    ArrayFacade CRules DePredSig SLibSig :=
  ⟨StorePtrAsElement CRules DePredSig SLibSig⟩


namespace ArrayFacade

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}

abbrev A (self : ArrayFacade CRules DePredSig SLibSig) :=
  self.elementStore.A

abbrev sizeA (self : ArrayFacade CRules DePredSig SLibSig) :=
  self.elementStore.sizeA

abbrev storeA (self : ArrayFacade CRules DePredSig SLibSig) :=
  self.elementStore.storeA

abbrev undefstoreA (self : ArrayFacade CRules DePredSig SLibSig) :=
  self.elementStore.undefstoreA

abbrev mixedstoreA (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixedstoreA self.elementStore

abbrev seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg self.elementStore

abbrev missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i self.elementStore

abbrev full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full self.elementStore

abbrev undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg self.elementStore

abbrev undef_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i self.elementStore

abbrev undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full self.elementStore

abbrev seg_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape self.elementStore

abbrev missing_i_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape self.elementStore

abbrev full_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape self.elementStore

abbrev mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg self.elementStore

abbrev mixed_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i self.elementStore

abbrev mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full self.elementStore

abbrev seg_split_to_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_split_to_missing_i self.elementStore

abbrev full_split_to_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_split_to_missing_i self.elementStore

abbrev mixed_seg_split_to_mixed_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_split_to_mixed_missing_i self.elementStore

abbrev mixed_full_split_to_mixed_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_mixed_missing_i self.elementStore

abbrev missing_i_merge_to_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_merge_to_seg self.elementStore

abbrev missing_i_merge_to_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_merge_to_full self.elementStore

abbrev mixed_missing_i_merge_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_mixed_seg self.elementStore

abbrev mixed_missing_i_merge_to_mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_mixed_full self.elementStore

abbrev undef_seg_split_to_undef_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_split_to_undef_missing_i self.elementStore

abbrev undef_full_split_to_undef_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_split_to_undef_missing_i self.elementStore

abbrev undef_missing_i_merge_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_merge_to_undef_seg self.elementStore

abbrev undef_missing_i_merge_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_merge_to_undef_full self.elementStore

abbrev mixed_seg_split_to_undef_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_split_to_undef_missing_i self.elementStore

abbrev mixed_full_split_to_undef_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_undef_missing_i self.elementStore

abbrev mixed_missing_i_merge_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_undef_seg self.elementStore

abbrev mixed_missing_i_merge_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_merge_to_undef_full self.elementStore

abbrev seg_shape_split_to_missing_i_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_split_to_missing_i_shape self.elementStore

abbrev full_shape_split_to_missing_i_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_split_to_missing_i_shape self.elementStore

abbrev missing_i_shape_merge_to_seg_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_merge_to_seg_shape self.elementStore

abbrev missing_i_shape_merge_to_full_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_merge_to_full_shape self.elementStore

abbrev seg_split_to_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_split_to_seg self.elementStore

abbrev mixed_seg_split_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_split_to_mixed_seg self.elementStore

abbrev undef_seg_split_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_split_to_undef_seg self.elementStore

abbrev seg_shape_split_to_seg_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_split_to_seg_shape self.elementStore

abbrev full_split_to_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_split_to_seg self.elementStore

abbrev mixed_full_split_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_mixed_seg self.elementStore

abbrev full_split_to_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_split_to_full self.elementStore

abbrev mixed_full_split_to_mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_split_to_mixed_full self.elementStore

abbrev undef_full_split_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_split_to_undef_seg self.elementStore

abbrev undef_full_split_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_split_to_undef_full self.elementStore

abbrev full_shape_split_to_seg_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_split_to_seg_shape self.elementStore

abbrev full_shape_split_to_full_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_split_to_full_shape self.elementStore

abbrev seg_merge_to_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_merge_to_seg self.elementStore

abbrev mixed_seg_merge_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_merge_to_mixed_seg self.elementStore

abbrev undef_seg_merge_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_merge_to_undef_seg self.elementStore

abbrev seg_shape_merge_to_seg_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_merge_to_seg_shape self.elementStore

abbrev seg_merge_to_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_merge_to_full self.elementStore

abbrev mixed_seg_merge_to_mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_merge_to_mixed_full self.elementStore

abbrev undef_seg_merge_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_merge_to_undef_full self.elementStore

abbrev seg_shape_merge_to_full_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_merge_to_full_shape self.elementStore

abbrev full_merge_to_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_merge_to_full self.elementStore

abbrev mixed_full_merge_to_mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_merge_to_mixed_full self.elementStore

abbrev undef_full_merge_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_merge_to_undef_full self.elementStore

abbrev full_shape_merge_to_full_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_merge_to_full_shape self.elementStore

abbrev full_to_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_seg self.elementStore

abbrev undef_full_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_undef_seg self.elementStore

abbrev full_shape_to_seg_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_to_seg_shape self.elementStore

abbrev mixed_full_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_mixed_seg self.elementStore

abbrev seg_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_mixed_seg self.elementStore

abbrev full_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_mixed_seg self.elementStore

abbrev mixed_seg_to_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_seg self.elementStore

abbrev missing_i_to_mixed_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_mixed_missing_i self.elementStore

abbrev mixed_missing_i_to_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_missing_i self.elementStore

abbrev undef_seg_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_to_mixed_seg self.elementStore

abbrev undef_full_to_mixed_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_mixed_seg self.elementStore

abbrev seg_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shift self.elementStore

abbrev mixed_seg_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_shift self.elementStore

abbrev seg_0_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_0_shift self.elementStore

abbrev mixed_seg_0_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_0_shift self.elementStore

abbrev undef_seg_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_shift self.elementStore

abbrev undef_seg_0_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_0_shift self.elementStore

abbrev seg_shape_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_shift self.elementStore

abbrev seg_shape_0_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_0_shift self.elementStore

abbrev seg_to_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_full self.elementStore

abbrev mixed_seg_to_mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_mixed_full self.elementStore

abbrev mixed_full_to_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_full self.elementStore

abbrev full_to_mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_mixed_full self.elementStore

abbrev undef_full_to_mixed_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_mixed_full self.elementStore

abbrev seg_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_undef_seg self.elementStore

abbrev mixed_seg_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_undef_seg self.elementStore

abbrev seg_to_seg_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_seg_shape self.elementStore

abbrev undef_seg_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_to_undef_full self.elementStore

abbrev seg_shape_to_full_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_to_full_shape self.elementStore

abbrev missing_i_to_seg_head (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_seg_head self.elementStore

abbrev mixed_missing_i_to_mixed_seg_head (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_mixed_seg_head self.elementStore

abbrev undef_missing_i_to_undef_seg_head (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_to_undef_seg_head self.elementStore

abbrev missing_i_shape_to_seg_shape_head (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_to_seg_shape_head self.elementStore

abbrev missing_i_to_undef_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_undef_missing_i self.elementStore

abbrev mixed_missing_i_to_undef_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_undef_missing_i self.elementStore

abbrev undef_missing_i_to_mixed_missing_i (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_to_mixed_missing_i self.elementStore

abbrev missing_i_to_missing_i_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_missing_i_shape self.elementStore

abbrev full_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_undef_full self.elementStore

abbrev mixed_seg_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_undef_full self.elementStore

abbrev mixed_full_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_undef_seg self.elementStore

abbrev mixed_full_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_undef_full self.elementStore

abbrev full_to_full_shape (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_full_shape self.elementStore

abbrev missing_i_to_seg_tail (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_to_seg_tail self.elementStore

abbrev mixed_missing_i_to_mixed_seg_tail (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_to_mixed_seg_tail self.elementStore

abbrev undef_missing_i_to_undef_seg_tail (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_to_undef_seg_tail self.elementStore

abbrev missing_i_shape_to_seg_shape_tail (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_to_seg_shape_tail self.elementStore

abbrev seg_shape_to_undef_seg (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_to_undef_seg self.elementStore

abbrev full_shape_to_undef_full (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_to_undef_full self.elementStore

abbrev undef_seg_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_to_align self.elementStore

abbrev seg_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_to_align self.elementStore

abbrev mixed_seg_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_to_align self.elementStore

abbrev seg_shape_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_to_align self.elementStore

abbrev full_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_to_align self.elementStore

abbrev mixed_full_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_to_align self.elementStore

abbrev undef_full_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_to_align self.elementStore

abbrev full_shape_to_align (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_to_align self.elementStore

abbrev undef_full_valid (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_valid self.elementStore

abbrev full_shape_valid (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_valid self.elementStore

abbrev seg_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_length_range self.elementStore

abbrev mixed_seg_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_length_range self.elementStore

abbrev undef_seg_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_length_range self.elementStore

abbrev seg_shape_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_length_range self.elementStore

abbrev full_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_length_range self.elementStore

abbrev mixed_full_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_length_range self.elementStore

abbrev undef_full_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_length_range self.elementStore

abbrev full_shape_length_range (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_length_range self.elementStore

abbrev mixedstoreA_to_undefstoreA (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixedstoreA_to_undefstoreA self.elementStore

abbrev mixedstoreA_shift (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixedstoreA_shift self.elementStore

abbrev seg_length (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_length self.elementStore

abbrev seg_Zlength (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_Zlength self.elementStore

abbrev seg_nil (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_nil self.elementStore

abbrev seg_single (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_single self.elementStore

abbrev mixed_seg_single (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_single self.elementStore

abbrev undef_seg_single (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_single self.elementStore

abbrev seg_shape_single (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_single self.elementStore

abbrev full_length (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_length self.elementStore

abbrev full_Zlength (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_Zlength self.elementStore

abbrev mixed_seg_length (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_length self.elementStore

abbrev mixed_seg_Zlength (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_Zlength self.elementStore

abbrev mixed_seg_nil (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_nil self.elementStore

abbrev mixed_full_length (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_length self.elementStore

abbrev mixed_full_Zlength (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_Zlength self.elementStore

abbrev mixed_missing_i_length (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_length self.elementStore

abbrev mixed_missing_i_Zlength (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_Zlength self.elementStore

abbrev missing_i_length (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_length self.elementStore

abbrev missing_i_Zlength (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_Zlength self.elementStore

abbrev seg_valid (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_valid self.elementStore

abbrev mixed_seg_valid (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_valid self.elementStore

abbrev undef_seg_valid (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_valid self.elementStore

abbrev seg_shape_valid (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_valid self.elementStore

abbrev seg_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_empty self.elementStore

abbrev mixed_seg_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_empty self.elementStore

abbrev undef_seg_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_empty self.elementStore

abbrev seg_shape_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_empty self.elementStore

abbrev seg_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_unfold self.elementStore

abbrev mixed_seg_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg_unfold self.elementStore

abbrev undef_seg_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg_unfold self.elementStore

abbrev seg_shape_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg_shape_unfold self.elementStore

abbrev missing_i_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_empty self.elementStore

abbrev mixed_missing_i_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_empty self.elementStore

abbrev undef_missing_i_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_empty self.elementStore

abbrev missing_i_shape_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_empty self.elementStore

abbrev missing_i_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_unfold self.elementStore

abbrev mixed_missing_i_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_missing_i_unfold self.elementStore

abbrev undef_missing_i_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_missing_i_unfold self.elementStore

abbrev missing_i_shape_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.missing_i_shape_unfold self.elementStore

abbrev full_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_empty self.elementStore

abbrev mixed_full_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_empty self.elementStore

abbrev undef_full_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_empty self.elementStore

abbrev full_shape_empty (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_empty self.elementStore

abbrev full_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_unfold self.elementStore

abbrev mixed_full_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full_unfold self.elementStore

abbrev undef_full_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full_unfold self.elementStore

abbrev full_shape_unfold (self : ArrayFacade CRules DePredSig SLibSig) :=
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full_shape_unfold self.elementStore

end ArrayFacade


end ArrayLibSig

export ArrayLibSig
  (StoreCharAsElement StoreUCharAsElement StoreShortAsElement
    StoreUShortAsElement StoreIntAsElement StoreUIntAsElement
    StoreInt64AsElement StoreUInt64AsElement StorePtrAsElement
    CharArray UCharArray ShortArray UShortArray IntArray UIntArray
    Int64Array UInt64Array PtrArray)

end SimpleC.SL.ArrayLib
