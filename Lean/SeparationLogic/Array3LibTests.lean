import SimpleC.SL.Array3Lib
import SimpleC.SL.Assertion
import Lean.Util.CollectAxioms

namespace Array3LibTests

open SimpleC.SL.Array2Lib.Array2LibSig
open SimpleC.SL.Array3Lib
open SimpleC.SL.Array3Lib.Array3LibSig
open SimpleC.SL.Array3LibCore.Array3LibCoreSig
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.Assertion
open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.StoreAux.StoreLibSig

open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "Array3 facade API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkArray3FacadeContract)
  "#check_array3_facade_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_array3_facade_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "Array3 facade API type hash changed: expected {expected}, got {actual}"
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
            throwError "Array3 facade declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"Array3 facade API contract verified for {names.size} declarations"

#check Array3LibSig
#check Array3LibSig.canonical
#check Array3Facade
#check CharArray3
#check UCharArray3
#check ShortArray3
#check UShortArray3
#check IntArray3
#check UIntArray3
#check Int64Array3
#check UInt64Array3
#check Int128Array3
#check UInt128Array3
#check FloatArray3
#check DoubleArray3
#check LongDoubleArray3
#check FiniteFloatArray3
#check FiniteDoubleArray3
#check FiniteLongDoubleArray3
#check PtrArray3

#check_array3_facade_contract [
  Array3LibSig,
  Array3LibSig.canonical,
  Array3Facade,
  CharArray3,
  UCharArray3,
  ShortArray3,
  UShortArray3,
  IntArray3,
  UIntArray3,
  Int64Array3,
  UInt64Array3,
  Int128Array3,
  UInt128Array3,
  FloatArray3,
  DoubleArray3,
  LongDoubleArray3,
  FiniteFloatArray3,
  FiniteDoubleArray3,
  FiniteLongDoubleArray3,
  PtrArray3,
  Array3Facade.A,
  Array3Facade.sizeA,
  Array3Facade.storeA,
  Array3Facade.undefstoreA,
  Array3Facade.plane_addr,
  Array3Facade.plane_store,
  Array3Facade.mixed_plane_store,
  Array3Facade.undef_plane_store,
  Array3Facade.full,
  Array3Facade.missing_i,
  Array3Facade.mixed_full,
  Array3Facade.mixed_missing_i,
  Array3Facade.undef_full,
  Array3Facade.undef_missing_i,
  Array3Facade.full_Zlength,
  Array3Facade.mixed_full_Zlength,
  Array3Facade.missing_i_Zlength,
  Array3Facade.mixed_missing_i_Zlength,
  Array3Facade.full_valid,
  Array3Facade.mixed_full_valid,
  Array3Facade.plane_store_to_undef_plane_store,
  Array3Facade.mixed_plane_store_to_undef_plane_store,
  Array3Facade.full_split_to_missing_i,
  Array3Facade.missing_i_merge_to_full,
  Array3Facade.mixed_full_split_to_mixed_missing_i,
  Array3Facade.mixed_missing_i_merge_to_mixed_full,
  Array3Facade.undef_full_split_to_undef_missing_i,
  Array3Facade.full_to_undef_full,
  Array3Facade.mixed_full_to_undef_full,
  Array3Facade.undef_full_valid
] => 15874636972443413654

noncomputable section

private abbrev TestDerived :=
  DerivedPredSig.canonical Arch32 BigEndian SL

private abbrev TestStore :=
  SimpleC.SL.StoreAux.StoreLibSig.canonical Arch32 BigEndian SL TestDerived

example : (CharArray3 Arch32 BigEndian SL TestDerived TestStore).A = Int := rfl
example : (Int128Array3 Arch32 BigEndian SL TestDerived TestStore).A = Int := rfl
example : (FloatArray3 Arch32 BigEndian SL TestDerived TestStore).A =
    SimpleC.SL.FloatLib.fp32 := rfl
example : (DoubleArray3 Arch32 BigEndian SL TestDerived TestStore).A =
    SimpleC.SL.FloatLib.fp64 := rfl
example : (LongDoubleArray3 Arch32 BigEndian SL TestDerived TestStore).A =
    SimpleC.SL.FloatLib.fp128 := rfl
example : (FiniteLongDoubleArray3 Arch32 BigEndian SL TestDerived TestStore).A =
    SimpleC.SL.FloatLib.fp128 := rfl
example : (PtrArray3 Arch32 BigEndian SL TestDerived TestStore).A = Int := rfl

example :
    (IntArray3 Arch32 BigEndian SL TestDerived TestStore).plane_addr 10 2 3 4 = 106 := rfl

example (x m k : Int) :
    (IntArray3 Arch32 BigEndian SL TestDerived TestStore).undef_full x (-1) m k =
      SL.andp (SL.coq_prop (0 = (-1 : Int))) SL.emp := rfl

example (x i m k : Int) (plane : List (List (Option Int))) :
    (IntArray3 Arch32 BigEndian SL TestDerived TestStore).mixed_plane_store
        m k x i plane =
      (IntArray2 Arch32 BigEndian SL TestDerived TestStore).mixed_full
        ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).plane_addr x m k i)
        m k plane := rfl

example (x i m k : Int) :
    (IntArray3 Arch32 BigEndian SL TestDerived TestStore).undef_missing_i
        x i 3 1 m k =
      store_undef_array_missing_i_rec SL
        ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).undef_plane_store m k)
        x i 3 1 0 := rfl

example (x i n m k : Int) (planes : List (List (List Int)))
    (h : 0 <= i ∧ i < n) :
    SL.derivable1
      ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).full x n m k planes)
      (SL.sepcon
        ((IntArray2 Arch32 BigEndian SL TestDerived TestStore).full
          ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).plane_addr x m k i)
          m k (AUXLib.Znth i planes []))
        ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).missing_i
          x i 0 n m k planes)) :=
  (IntArray3 Arch32 BigEndian SL TestDerived TestStore).full_split_to_missing_i
    x i n m k planes h

example (x i n m k : Int) (planes : List (List (List (Option Int))))
    (h : 0 <= i ∧ i < n) :
    SL.derivable1
      ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).mixed_full
        x n m k planes)
      (SL.sepcon
        ((IntArray2 Arch32 BigEndian SL TestDerived TestStore).mixed_full
          ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).plane_addr x m k i)
          m k (AUXLib.Znth i planes []))
        ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).mixed_missing_i
          x i 0 n m k planes)) :=
  (IntArray3 Arch32 BigEndian SL TestDerived TestStore).mixed_full_split_to_mixed_missing_i
    x i n m k planes h

example (x n m k : Int) (planes : List (List (List Int))) :
    SL.derivable1
      ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).full
        x n m k planes)
      ((IntArray3 Arch32 BigEndian SL TestDerived TestStore).undef_full
        x n m k) :=
  (IntArray3 Arch32 BigEndian SL TestDerived TestStore).full_to_undef_full
    x n m k planes

#print axioms SimpleC.SL.Array3Lib.Array3LibSig.IntArray3
#print axioms SimpleC.SL.Array3Lib.Array3LibSig.FloatArray3
#print axioms SimpleC.SL.Array3Lib.Array3LibSig.PtrArray3

end

end Array3LibTests
