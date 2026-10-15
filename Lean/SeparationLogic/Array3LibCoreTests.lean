import SimpleC.SL.Array3LibCore
import SimpleC.SL.Assertion
import Lean.Util.CollectAxioms

namespace Array3LibCoreTests

open SimpleC.SL.Array2LibCore.Array2LibCoreSig
open SimpleC.SL.Array3LibCore
open SimpleC.SL.Array3LibCore.Array3LibCoreSig
open SimpleC.SL.Array3LibCore.Array3LibCoreSig.Array3Lib
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
      | throwError "Array3 core API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkArray3CoreContract)
  "#check_array3_core_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_array3_core_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "Array3 core API type hash changed: expected {expected}, got {actual}"
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
            throwError "Array3 core declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"Array3 core API contract verified for {names.size} declarations"

#check Array3LibCoreSig
#check Array3LibCoreSig.canonical
#check PlaneArray
#check plane_addr
#check plane_store
#check mixed_plane_store
#check undef_plane_store
#check full
#check missing_i
#check mixed_full
#check mixed_missing_i
#check undef_full
#check undef_missing_i
#check full_Zlength
#check mixed_full_Zlength
#check missing_i_Zlength
#check mixed_missing_i_Zlength
#check full_valid
#check mixed_full_valid
#check plane_store_to_undef_plane_store
#check mixed_plane_store_to_undef_plane_store
#check full_split_to_missing_i
#check missing_i_merge_to_full
#check mixed_full_split_to_mixed_missing_i
#check mixed_missing_i_merge_to_mixed_full
#check undef_full_split_to_undef_missing_i
#check full_to_undef_full
#check mixed_full_to_undef_full
#check undef_full_valid

#check_array3_core_contract [
  Array3LibCoreSig,
  Array3LibCoreSig.canonical,
  PlaneArray,
  plane_addr,
  plane_store,
  mixed_plane_store,
  undef_plane_store,
  full,
  missing_i,
  mixed_full,
  mixed_missing_i,
  undef_full,
  undef_missing_i,
  full_Zlength,
  mixed_full_Zlength,
  missing_i_Zlength,
  mixed_missing_i_Zlength,
  full_valid,
  mixed_full_valid,
  plane_store_to_undef_plane_store,
  mixed_plane_store_to_undef_plane_store,
  full_split_to_missing_i,
  missing_i_merge_to_full,
  mixed_full_split_to_mixed_missing_i,
  mixed_missing_i_merge_to_mixed_full,
  undef_full_split_to_undef_missing_i,
  full_to_undef_full,
  mixed_full_to_undef_full,
  undef_full_valid
] => 9284154030120932449

noncomputable section

private abbrev TestDerived :=
  DerivedPredSig.canonical Arch32 BigEndian SL

private abbrev TestStore :=
  SimpleC.SL.StoreAux.StoreLibSig.canonical Arch32 BigEndian SL TestDerived

private noncomputable abbrev TestElement :=
  StoreIntAsElement Arch32 BigEndian SL TestDerived TestStore

example (x n m : Int) (plane : List (List Int)) :
    (PlaneArray TestElement).full x n m plane =
      Array2Lib.full TestElement x n m plane := rfl

example : plane_addr TestElement 10 2 3 4 = 106 := rfl

example (x n m k : Int) (planes : List (List (List Int))) :
    full TestElement x n m k planes =
      store_array SL (plane_store TestElement m k) x n planes := rfl

example (x i m k : Int) (plane : List (List (Option Int))) :
    mixed_plane_store TestElement m k x i plane =
      Array2Lib.mixed_full TestElement (plane_addr TestElement x m k i) m k plane := rfl

example (x i lo hi m k : Int) (planes : List (List (List Int))) :
    missing_i TestElement x i lo hi m k planes =
      store_array_missing_i_rec SL (plane_store TestElement m k)
        x i lo hi planes := rfl

example (x i lo hi m k : Int)
    (planes : List (List (List (Option Int)))) :
    mixed_missing_i TestElement x i lo hi m k planes =
      store_array_missing_i_rec SL (mixed_plane_store TestElement m k)
        x i lo hi planes := rfl

example (x m k : Int) :
    undef_full TestElement x (-1) m k =
      SL.andp (SL.coq_prop (0 = (-1 : Int))) SL.emp := rfl

example (x i m k : Int) :
    undef_missing_i TestElement x i 3 1 m k =
      store_undef_array_missing_i_rec SL (undef_plane_store TestElement m k)
        x i 3 1 0 := rfl

example (x i n m k : Int) (planes : List (List (List Int)))
    (h : 0 <= i ∧ i < n) :
    SL.derivable1 (full TestElement x n m k planes)
      (SL.sepcon
        (Array2Lib.full TestElement (plane_addr TestElement x m k i)
          m k (AUXLib.Znth i planes []))
        (missing_i TestElement x i 0 n m k planes)) :=
  full_split_to_missing_i TestElement x i n m k planes h

example (x i n m k : Int) (planes : List (List (List Int)))
    (plane : List (List Int)) (h : 0 <= i ∧ i < n) :
    SL.derivable1
      (SL.sepcon
        (Array2Lib.full TestElement (plane_addr TestElement x m k i) m k plane)
        (missing_i TestElement x i 0 n m k planes))
      (full TestElement x n m k (AUXLib.replace_Znth i plane planes)) :=
  missing_i_merge_to_full TestElement x i n m k planes plane h

example (x i n m k : Int) (planes : List (List (List (Option Int))))
    (h : 0 <= i ∧ i < n) :
    SL.derivable1 (mixed_full TestElement x n m k planes)
      (SL.sepcon
        (Array2Lib.mixed_full TestElement (plane_addr TestElement x m k i)
          m k (AUXLib.Znth i planes []))
        (mixed_missing_i TestElement x i 0 n m k planes)) :=
  mixed_full_split_to_mixed_missing_i TestElement x i n m k planes h

example (x i n m k : Int) (planes : List (List (List (Option Int))))
    (plane : List (List (Option Int))) (h : 0 <= i ∧ i < n) :
    SL.derivable1
      (SL.sepcon
        (Array2Lib.mixed_full TestElement (plane_addr TestElement x m k i) m k plane)
        (mixed_missing_i TestElement x i 0 n m k planes))
      (mixed_full TestElement x n m k (AUXLib.replace_Znth i plane planes)) :=
  mixed_missing_i_merge_to_mixed_full TestElement x i n m k planes plane h

example (x i n m k : Int) (h : 0 <= i ∧ i < n) :
    SL.derivable1 (undef_full TestElement x n m k)
      (SL.sepcon
        (Array2Lib.undef_full TestElement (plane_addr TestElement x m k i) m k)
        (undef_missing_i TestElement x i 0 n m k)) :=
  undef_full_split_to_undef_missing_i TestElement x i n m k h

example (x m k i : Int) (plane : List (List Int)) :
    SL.derivable1 (plane_store TestElement m k x i plane)
      (undef_plane_store TestElement m k x i) :=
  plane_store_to_undef_plane_store TestElement x m k i plane

example (x m k i : Int) (plane : List (List (Option Int))) :
    SL.derivable1 (mixed_plane_store TestElement m k x i plane)
      (undef_plane_store TestElement m k x i) :=
  mixed_plane_store_to_undef_plane_store TestElement x m k i plane

example (x n m k : Int) (planes : List (List (List Int))) :
    SL.derivable1 (full TestElement x n m k planes)
      (undef_full TestElement x n m k) :=
  full_to_undef_full TestElement x n m k planes

example (x n m k : Int) (planes : List (List (List (Option Int)))) :
    SL.derivable1 (mixed_full TestElement x n m k planes)
      (undef_full TestElement x n m k) :=
  mixed_full_to_undef_full TestElement x n m k planes

#print axioms SimpleC.SL.Array3LibCore.Array3LibCoreSig.Array3Lib.full_split_to_missing_i
#print axioms SimpleC.SL.Array3LibCore.Array3LibCoreSig.Array3Lib.undef_full_valid

end

end Array3LibCoreTests
