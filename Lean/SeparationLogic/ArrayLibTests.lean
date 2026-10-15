import SimpleC.SL.ArrayLib

namespace ArrayLibTests

open SimpleC.SL.CArch
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.DerivedPredSigCompat
open SimpleC.SL.CNotation
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig

open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "ArrayLib facade API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkArrayLibFacadeContract)
  "#check_array_lib_facade_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_array_lib_facade_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "ArrayLib facade API type hash changed: expected {expected}, got {actual}"
      logInfo m!"ArrayLib facade API contract verified for {names.size} declarations"

-- Freeze the module counterpart, 17 element stores, 17 concrete arrays, the
-- elementStore projection, and every public ArrayFacade projection/method.
#check_array_lib_facade_contract [
  ArrayLibSig,
  ArrayLibSig.canonical,
  StoreCharAsElement,
  StoreUCharAsElement,
  StoreShortAsElement,
  StoreUShortAsElement,
  StoreIntAsElement,
  StoreUIntAsElement,
  StoreInt64AsElement,
  StoreUInt64AsElement,
  StoreInt128AsElement,
  StoreUInt128AsElement,
  StorePtrAsElement,
  StoreFloatAsElement,
  StoreDoubleAsElement,
  StoreLongDoubleAsElement,
  StoreFiniteFloatAsElement,
  StoreFiniteDoubleAsElement,
  StoreFiniteLongDoubleAsElement,
  ArrayFacade,
  ArrayFacade.elementStore,
  CharArray,
  UCharArray,
  ShortArray,
  UShortArray,
  IntArray,
  UIntArray,
  Int64Array,
  UInt64Array,
  Int128Array,
  UInt128Array,
  PtrArray,
  ArrayLibSig.FloatArray,
  DoubleArray,
  LongDoubleArray,
  FiniteFloatArray,
  FiniteDoubleArray,
  FiniteLongDoubleArray,
  ArrayFacade.A,
  ArrayFacade.sizeA,
  ArrayFacade.storeA,
  ArrayFacade.undefstoreA,
  ArrayFacade.mixedstoreA,
  ArrayFacade.seg,
  ArrayFacade.missing_i,
  ArrayFacade.full,
  ArrayFacade.undef_seg,
  ArrayFacade.undef_missing_i,
  ArrayFacade.undef_full,
  ArrayFacade.seg_shape,
  ArrayFacade.missing_i_shape,
  ArrayFacade.full_shape,
  ArrayFacade.mixed_seg,
  ArrayFacade.mixed_missing_i,
  ArrayFacade.mixed_full,
  ArrayFacade.seg_split_to_missing_i,
  ArrayFacade.full_split_to_missing_i,
  ArrayFacade.mixed_seg_split_to_mixed_missing_i,
  ArrayFacade.mixed_full_split_to_mixed_missing_i,
  ArrayFacade.missing_i_merge_to_seg,
  ArrayFacade.missing_i_merge_to_full,
  ArrayFacade.mixed_missing_i_merge_to_mixed_seg,
  ArrayFacade.mixed_missing_i_merge_to_mixed_full,
  ArrayFacade.undef_seg_split_to_undef_missing_i,
  ArrayFacade.undef_full_split_to_undef_missing_i,
  ArrayFacade.undef_missing_i_merge_to_undef_seg,
  ArrayFacade.undef_missing_i_merge_to_undef_full,
  ArrayFacade.mixed_seg_split_to_undef_missing_i,
  ArrayFacade.mixed_full_split_to_undef_missing_i,
  ArrayFacade.mixed_missing_i_merge_to_undef_seg,
  ArrayFacade.mixed_missing_i_merge_to_undef_full,
  ArrayFacade.seg_shape_split_to_missing_i_shape,
  ArrayFacade.full_shape_split_to_missing_i_shape,
  ArrayFacade.missing_i_shape_merge_to_seg_shape,
  ArrayFacade.missing_i_shape_merge_to_full_shape,
  ArrayFacade.seg_split_to_seg,
  ArrayFacade.mixed_seg_split_to_mixed_seg,
  ArrayFacade.undef_seg_split_to_undef_seg,
  ArrayFacade.seg_shape_split_to_seg_shape,
  ArrayFacade.full_split_to_seg,
  ArrayFacade.mixed_full_split_to_mixed_seg,
  ArrayFacade.full_split_to_full,
  ArrayFacade.mixed_full_split_to_mixed_full,
  ArrayFacade.undef_full_split_to_undef_seg,
  ArrayFacade.undef_full_split_to_undef_full,
  ArrayFacade.full_shape_split_to_seg_shape,
  ArrayFacade.full_shape_split_to_full_shape,
  ArrayFacade.seg_merge_to_seg,
  ArrayFacade.mixed_seg_merge_to_mixed_seg,
  ArrayFacade.undef_seg_merge_to_undef_seg,
  ArrayFacade.seg_shape_merge_to_seg_shape,
  ArrayFacade.seg_merge_to_full,
  ArrayFacade.mixed_seg_merge_to_mixed_full,
  ArrayFacade.undef_seg_merge_to_undef_full,
  ArrayFacade.seg_shape_merge_to_full_shape,
  ArrayFacade.full_merge_to_full,
  ArrayFacade.mixed_full_merge_to_mixed_full,
  ArrayFacade.undef_full_merge_to_undef_full,
  ArrayFacade.full_shape_merge_to_full_shape,
  ArrayFacade.full_to_seg,
  ArrayFacade.undef_full_to_undef_seg,
  ArrayFacade.full_shape_to_seg_shape,
  ArrayFacade.mixed_full_to_mixed_seg,
  ArrayFacade.seg_to_mixed_seg,
  ArrayFacade.full_to_mixed_seg,
  ArrayFacade.mixed_seg_to_seg,
  ArrayFacade.missing_i_to_mixed_missing_i,
  ArrayFacade.mixed_missing_i_to_missing_i,
  ArrayFacade.undef_seg_to_mixed_seg,
  ArrayFacade.undef_full_to_mixed_seg,
  ArrayFacade.seg_shift,
  ArrayFacade.mixed_seg_shift,
  ArrayFacade.seg_0_shift,
  ArrayFacade.mixed_seg_0_shift,
  ArrayFacade.undef_seg_shift,
  ArrayFacade.undef_seg_0_shift,
  ArrayFacade.seg_shape_shift,
  ArrayFacade.seg_shape_0_shift,
  ArrayFacade.seg_to_full,
  ArrayFacade.mixed_seg_to_mixed_full,
  ArrayFacade.mixed_full_to_full,
  ArrayFacade.full_to_mixed_full,
  ArrayFacade.undef_full_to_mixed_full,
  ArrayFacade.seg_to_undef_seg,
  ArrayFacade.mixed_seg_to_undef_seg,
  ArrayFacade.seg_to_seg_shape,
  ArrayFacade.undef_seg_to_undef_full,
  ArrayFacade.seg_shape_to_full_shape,
  ArrayFacade.missing_i_to_seg_head,
  ArrayFacade.mixed_missing_i_to_mixed_seg_head,
  ArrayFacade.undef_missing_i_to_undef_seg_head,
  ArrayFacade.missing_i_shape_to_seg_shape_head,
  ArrayFacade.missing_i_to_undef_missing_i,
  ArrayFacade.mixed_missing_i_to_undef_missing_i,
  ArrayFacade.undef_missing_i_to_mixed_missing_i,
  ArrayFacade.missing_i_to_missing_i_shape,
  ArrayFacade.full_to_undef_full,
  ArrayFacade.mixed_seg_to_undef_full,
  ArrayFacade.mixed_full_to_undef_seg,
  ArrayFacade.mixed_full_to_undef_full,
  ArrayFacade.full_to_full_shape,
  ArrayFacade.missing_i_to_seg_tail,
  ArrayFacade.mixed_missing_i_to_mixed_seg_tail,
  ArrayFacade.undef_missing_i_to_undef_seg_tail,
  ArrayFacade.missing_i_shape_to_seg_shape_tail,
  ArrayFacade.seg_shape_to_undef_seg,
  ArrayFacade.full_shape_to_undef_full,
  ArrayFacade.undef_seg_to_align,
  ArrayFacade.seg_to_align,
  ArrayFacade.mixed_seg_to_align,
  ArrayFacade.seg_shape_to_align,
  ArrayFacade.full_to_align,
  ArrayFacade.mixed_full_to_align,
  ArrayFacade.undef_full_to_align,
  ArrayFacade.full_shape_to_align,
  ArrayFacade.undef_full_valid,
  ArrayFacade.full_shape_valid,
  ArrayFacade.seg_length_range,
  ArrayFacade.mixed_seg_length_range,
  ArrayFacade.undef_seg_length_range,
  ArrayFacade.seg_shape_length_range,
  ArrayFacade.full_length_range,
  ArrayFacade.mixed_full_length_range,
  ArrayFacade.undef_full_length_range,
  ArrayFacade.full_shape_length_range,
  ArrayFacade.mixedstoreA_to_undefstoreA,
  ArrayFacade.mixedstoreA_shift,
  ArrayFacade.seg_length,
  ArrayFacade.seg_Zlength,
  ArrayFacade.seg_nil,
  ArrayFacade.seg_single,
  ArrayFacade.mixed_seg_single,
  ArrayFacade.undef_seg_single,
  ArrayFacade.seg_shape_single,
  ArrayFacade.full_length,
  ArrayFacade.full_Zlength,
  ArrayFacade.mixed_seg_length,
  ArrayFacade.mixed_seg_Zlength,
  ArrayFacade.mixed_seg_nil,
  ArrayFacade.mixed_full_length,
  ArrayFacade.mixed_full_Zlength,
  ArrayFacade.mixed_missing_i_length,
  ArrayFacade.mixed_missing_i_Zlength,
  ArrayFacade.missing_i_length,
  ArrayFacade.missing_i_Zlength,
  ArrayFacade.seg_valid,
  ArrayFacade.mixed_seg_valid,
  ArrayFacade.undef_seg_valid,
  ArrayFacade.seg_shape_valid,
  ArrayFacade.seg_empty,
  ArrayFacade.mixed_seg_empty,
  ArrayFacade.undef_seg_empty,
  ArrayFacade.seg_shape_empty,
  ArrayFacade.seg_unfold,
  ArrayFacade.mixed_seg_unfold,
  ArrayFacade.undef_seg_unfold,
  ArrayFacade.seg_shape_unfold,
  ArrayFacade.missing_i_empty,
  ArrayFacade.mixed_missing_i_empty,
  ArrayFacade.undef_missing_i_empty,
  ArrayFacade.missing_i_shape_empty,
  ArrayFacade.missing_i_unfold,
  ArrayFacade.mixed_missing_i_unfold,
  ArrayFacade.undef_missing_i_unfold,
  ArrayFacade.missing_i_shape_unfold,
  ArrayFacade.full_empty,
  ArrayFacade.mixed_full_empty,
  ArrayFacade.undef_full_empty,
  ArrayFacade.full_shape_empty,
  ArrayFacade.full_unfold,
  ArrayFacade.mixed_full_unfold,
  ArrayFacade.undef_full_unfold,
  ArrayFacade.full_shape_unfold
] => 17966682614900592657

#check ArrayLibSig
#check ArrayLibSig.canonical
#check ArrayFacade
#check StoreCharAsElement
#check StoreUCharAsElement
#check StoreShortAsElement
#check StoreUShortAsElement
#check StoreIntAsElement
#check StoreUIntAsElement
#check StoreInt64AsElement
#check StoreUInt64AsElement
#check StoreInt128AsElement
#check StoreUInt128AsElement
#check StoreFloatAsElement
#check StoreDoubleAsElement
#check StoreLongDoubleAsElement
#check StoreFiniteFloatAsElement
#check StoreFiniteDoubleAsElement
#check StoreFiniteLongDoubleAsElement
#check StorePtrAsElement
#check CharArray
#check UCharArray
#check ShortArray
#check UShortArray
#check IntArray
#check UIntArray
#check Int64Array
#check UInt64Array
#check Int128Array
#check UInt128Array
#check FloatArray
#check DoubleArray
#check LongDoubleArray
#check FiniteFloatArray
#check FiniteDoubleArray
#check FiniteLongDoubleArray
#check PtrArray

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSigCompat.Sig CRules}
variable {SLibSig : StoreLibSigCompat CRules DePredSig}

example : (StoreCharAsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUCharAsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreShortAsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUShortAsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreIntAsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUIntAsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreInt64AsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUInt64AsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreInt128AsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUInt128AsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (StoreFloatAsElement Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp32 := rfl
example : (StoreDoubleAsElement Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp64 := rfl
example : (StoreLongDoubleAsElement Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp128 := rfl
example : (StoreFiniteFloatAsElement Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp32 := rfl
example : (StoreFiniteDoubleAsElement Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp64 := rfl
example : (StoreFiniteLongDoubleAsElement Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp128 := rfl
example : (StorePtrAsElement Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl

example (x lo a : Int) :
    (StoreCharAsElement Arch32 BigEndian CRules DePredSig SLibSig).storeA x lo a =
      store_char CRules
        (x + lo * sizeof_front_end_type FET_char) a := rfl

example (x lo a : Int) :
    (StorePtrAsElement Arch32 BigEndian CRules DePredSig SLibSig).storeA x lo a =
      store_ptr CRules (x + lo * 4) a := rfl

#check (CharArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (CharArray Arch32 BigEndian CRules DePredSig SLibSig).seg_split_to_seg
#check (UCharArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (ShortArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (UShortArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (IntArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (IntArray Arch32 BigEndian CRules DePredSig SLibSig).full_split_to_full
#check (IntArray Arch32 BigEndian CRules DePredSig SLibSig).full_merge_to_full
#check (IntArray Arch32 BigEndian CRules DePredSig SLibSig).full_length_range
#check (UIntArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (Int64Array Arch32 BigEndian CRules DePredSig SLibSig).full
#check (UInt64Array Arch32 BigEndian CRules DePredSig SLibSig).full
#check (Int128Array Arch32 BigEndian CRules DePredSig SLibSig).full
#check (UInt128Array Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FloatArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (DoubleArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (LongDoubleArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FiniteFloatArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FiniteDoubleArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FiniteLongDoubleArray Arch32 BigEndian CRules DePredSig SLibSig).full
#check (PtrArray Arch32 BigEndian CRules DePredSig SLibSig).full

example (x n : Int) (l : List Int) :
    CRules.derivable1
      ((IntArray Arch32 BigEndian CRules DePredSig SLibSig).full x n l)
      ((IntArray Arch32 BigEndian CRules DePredSig SLibSig).seg x 0 n l) :=
  (IntArray Arch32 BigEndian CRules DePredSig SLibSig).full_to_seg x n l

example (x n : Int) :
    CRules.logic_equiv
      ((IntArray Arch32 BigEndian CRules DePredSig SLibSig).full x n [])
      (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo : Int) :
    CRules.logic_equiv
      ((PtrArray Arch32 BigEndian CRules DePredSig SLibSig).undef_seg x lo lo)
      CRules.emp := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (n : Int) :
    CRules.logic_equiv
      (CRules.exp Int fun x =>
        (IntArray Arch32 BigEndian CRules DePredSig SLibSig).full x n [])
      (CRules.exp Int fun _ =>
        CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (n : Int) :
    CRules.logic_equiv
      (CRules.exp Int fun x =>
        CRules.sepcon
          ((IntArray Arch32 BigEndian CRules DePredSig SLibSig).full x n [])
          ((IntArray Arch32 BigEndian CRules DePredSig SLibSig).full x n []))
      (CRules.exp Int fun _ =>
        CRules.sepcon
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (n : Int) :
    CRules.logic_equiv
      (CRules.allp Int fun x =>
        CRules.sepcon
          ((IntArray Arch32 BigEndian CRules DePredSig SLibSig).full x n [])
          ((IntArray Arch32 BigEndian CRules DePredSig SLibSig).full x n []))
      (CRules.allp Int fun _ =>
        CRules.sepcon
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

set_option maxHeartbeats 1000000 in
example (n : Int) (h : n >= 0) :
    CRules.logic_equiv
      (CRules.exp Int fun x =>
        CRules.sepcon
          ((PtrArray Arch32 BigEndian CRules DePredSig SLibSig).undef_full x (n + 1))
          ((PtrArray Arch32 BigEndian CRules DePredSig SLibSig).undef_full x (n + 1)))
      (CRules.exp Int fun x =>
        CRules.sepcon
          (CRules.sepcon
            ((PtrArray Arch32 BigEndian CRules DePredSig SLibSig).undefstoreA x 0)
            ((PtrArray Arch32 BigEndian CRules DePredSig SLibSig).undef_seg x 1 (n + 1)))
          (CRules.sepcon
            ((PtrArray Arch32 BigEndian CRules DePredSig SLibSig).undefstoreA x 0)
            ((PtrArray Arch32 BigEndian CRules DePredSig SLibSig).undef_seg x 1 (n + 1)))) := by
  ArraySimplify
  · exact CRules.toContext.logic_equiv_refl _
  · exact h
  · exact h

end

#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StoreCharAsElement
#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StoreIntAsElement
#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StoreFloatAsElement
#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StoreFiniteLongDoubleAsElement
#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StorePtrAsElement

end ArrayLibTests
