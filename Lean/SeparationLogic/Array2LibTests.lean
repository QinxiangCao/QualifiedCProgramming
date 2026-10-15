import SimpleC.SL.Array2Lib
import Lean.Util.CollectAxioms

namespace Array2LibTests

open SimpleC.SL.CArch
open SimpleC.SL.Array2Lib
open SimpleC.SL.Array2Lib.Array2LibSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.DerivedPredSigCompat
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig

open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env ← getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "Array2 facade API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkArray2FacadeContract)
  "#check_array2_facade_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_array2_facade_contract [$ids:ident,*] => $expected:num) => do
      let names ← resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual ← apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "Array2 facade API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[
        ``propext,
        ``Classical.choice,
        ``Quot.sound,
        ``SimpleC.SL.CNotation.sizeof_struct_type,
        ``SimpleC.SL.CNotation.sizeof_union_type,
        ``SimpleC.SL.CNotation.sizeof_enum_type,
        ``SimpleC.SL.CNotation.sizeof_alias_type]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "Array2 facade declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"Array2 facade API contract verified for {names.size} declarations"

#check Array2LibSig
#check Array2LibSig.canonical
#check Array2Facade
#check CharArray2
#check UCharArray2
#check ShortArray2
#check UShortArray2
#check IntArray2
#check UIntArray2
#check Int64Array2
#check UInt64Array2
#check Int128Array2
#check UInt128Array2
#check FloatArray2
#check DoubleArray2
#check LongDoubleArray2
#check FiniteFloatArray2
#check FiniteDoubleArray2
#check FiniteLongDoubleArray2
#check PtrArray2

#check Array2Facade.A
#check Array2Facade.sizeA
#check Array2Facade.storeA
#check Array2Facade.undefstoreA
#check Array2Facade.row_addr
#check Array2Facade.row_store
#check Array2Facade.mixed_row_store
#check Array2Facade.undef_row_store
#check Array2Facade.full
#check Array2Facade.missing_i
#check Array2Facade.mixed_full
#check Array2Facade.mixed_missing_i
#check Array2Facade.undef_full
#check Array2Facade.undef_missing_i
#check Array2Facade.full_Zlength
#check Array2Facade.mixed_full_Zlength
#check Array2Facade.missing_i_Zlength
#check Array2Facade.mixed_missing_i_Zlength
#check Array2Facade.full_valid
#check Array2Facade.mixed_full_valid
#check Array2Facade.row_store_to_undef_row_store
#check Array2Facade.mixed_row_store_to_undef_row_store
#check Array2Facade.full_split_to_missing_i
#check Array2Facade.missing_i_merge_to_full
#check Array2Facade.mixed_full_split_to_mixed_missing_i
#check Array2Facade.mixed_missing_i_merge_to_mixed_full
#check Array2Facade.undef_full_split_to_undef_missing_i
#check Array2Facade.full_to_undef_full
#check Array2Facade.mixed_full_to_undef_full
#check Array2Facade.undef_full_valid

-- The manifest freezes the module counterpart, all 17 concrete instances, and all
-- all facade projections and methods. Its whitelist contains only Lean foundations and source
-- CNotation size assumptions already recorded in the migration log.
#check_array2_facade_contract [
  Array2LibSig,
  Array2LibSig.canonical,
  Array2Facade,
  CharArray2,
  UCharArray2,
  ShortArray2,
  UShortArray2,
  IntArray2,
  UIntArray2,
  Int64Array2,
  UInt64Array2,
  Int128Array2,
  UInt128Array2,
  FloatArray2,
  DoubleArray2,
  LongDoubleArray2,
  FiniteFloatArray2,
  FiniteDoubleArray2,
  FiniteLongDoubleArray2,
  PtrArray2,
  Array2Facade.A,
  Array2Facade.sizeA,
  Array2Facade.storeA,
  Array2Facade.undefstoreA,
  Array2Facade.row_addr,
  Array2Facade.row_store,
  Array2Facade.mixed_row_store,
  Array2Facade.undef_row_store,
  Array2Facade.full,
  Array2Facade.missing_i,
  Array2Facade.mixed_full,
  Array2Facade.mixed_missing_i,
  Array2Facade.undef_full,
  Array2Facade.undef_missing_i,
  Array2Facade.full_Zlength,
  Array2Facade.mixed_full_Zlength,
  Array2Facade.missing_i_Zlength,
  Array2Facade.mixed_missing_i_Zlength,
  Array2Facade.full_valid,
  Array2Facade.mixed_full_valid,
  Array2Facade.row_store_to_undef_row_store,
  Array2Facade.mixed_row_store_to_undef_row_store,
  Array2Facade.full_split_to_missing_i,
  Array2Facade.missing_i_merge_to_full,
  Array2Facade.mixed_full_split_to_mixed_missing_i,
  Array2Facade.mixed_missing_i_merge_to_mixed_full,
  Array2Facade.undef_full_split_to_undef_missing_i,
  Array2Facade.full_to_undef_full,
  Array2Facade.mixed_full_to_undef_full,
  Array2Facade.undef_full_valid
] => 17416283619110893990

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSigCompat.Sig CRules}
variable {SLibSig : StoreLibSigCompat CRules DePredSig}

example : (CharArray2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (UCharArray2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (ShortArray2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (UShortArray2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (IntArray2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (UIntArray2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (Int64Array2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (UInt64Array2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (Int128Array2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (UInt128Array2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl
example : (FloatArray2 Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp32 := rfl
example : (DoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp64 := rfl
example : (LongDoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp128 := rfl
example : (FiniteFloatArray2 Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp32 := rfl
example : (FiniteDoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp64 := rfl
example : (FiniteLongDoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).A =
    SimpleC.SL.FloatLib.fp128 := rfl
example : (PtrArray2 Arch32 BigEndian CRules DePredSig SLibSig).A = Int := rfl

#check (CharArray2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (UCharArray2 Arch32 BigEndian CRules DePredSig SLibSig).mixed_full
#check (ShortArray2 Arch32 BigEndian CRules DePredSig SLibSig).missing_i
#check (UShortArray2 Arch32 BigEndian CRules DePredSig SLibSig).undef_full
#check (IntArray2 Arch32 BigEndian CRules DePredSig SLibSig).full_split_to_missing_i
#check (UIntArray2 Arch32 BigEndian CRules DePredSig SLibSig).missing_i_merge_to_full
#check (Int64Array2 Arch32 BigEndian CRules DePredSig SLibSig).full_to_undef_full
#check (UInt64Array2 Arch32 BigEndian CRules DePredSig SLibSig).mixed_full_to_undef_full
#check (Int128Array2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (UInt128Array2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FloatArray2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (DoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (LongDoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FiniteFloatArray2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FiniteDoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (FiniteLongDoubleArray2 Arch32 BigEndian CRules DePredSig SLibSig).full
#check (PtrArray2 Arch32 BigEndian CRules DePredSig SLibSig).undef_full_valid

example (x m i : Int) :
    (IntArray2 Arch32 BigEndian CRules DePredSig SLibSig).row_addr x m i =
      x + i * m *
        (SimpleC.SL.ArrayLib.ArrayLibSig.StoreIntAsElement
          Arch32 BigEndian CRules DePredSig SLibSig).sizeA := rfl

example (x i n m : Int) (rows : List (List Int)) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 ((IntArray2 Arch32 BigEndian CRules DePredSig SLibSig).full x n m rows)
      (CRules.sepcon
        ((SimpleC.SL.ArrayLib.ArrayLibSig.IntArray
          Arch32 BigEndian CRules DePredSig SLibSig).full
          ((IntArray2 Arch32 BigEndian CRules DePredSig SLibSig).row_addr x m i)
          m (AUXLib.Znth i rows []))
        ((IntArray2 Arch32 BigEndian CRules DePredSig SLibSig).missing_i x i 0 n m rows)) :=
  (IntArray2 Arch32 BigEndian CRules DePredSig SLibSig).full_split_to_missing_i
    x i n m rows h

example (x i n m : Int) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 ((PtrArray2 Arch32 BigEndian CRules DePredSig SLibSig).undef_full x n m)
      (CRules.sepcon
        ((SimpleC.SL.ArrayLib.ArrayLibSig.PtrArray
          Arch32 BigEndian CRules DePredSig SLibSig).undef_full
          ((PtrArray2 Arch32 BigEndian CRules DePredSig SLibSig).row_addr x m i) m)
        ((PtrArray2 Arch32 BigEndian CRules DePredSig SLibSig).undef_missing_i x i 0 n m)) :=
  (PtrArray2 Arch32 BigEndian CRules DePredSig SLibSig).undef_full_split_to_undef_missing_i
    x i n m h

end


#print axioms SimpleC.SL.Array2Lib.Array2LibSig.IntArray2
#print axioms SimpleC.SL.Array2Lib.Array2LibSig.FloatArray2
#print axioms SimpleC.SL.Array2Lib.Array2LibSig.PtrArray2

end Array2LibTests
