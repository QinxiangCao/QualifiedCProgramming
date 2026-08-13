import SimpleC.SL.Array2LibCore
import Lean.Util.CollectAxioms

namespace Array2LibCoreTests

open AUXLib
open SimpleC.SL.Array2LibCore
open SimpleC.SL.Array2LibCore.Array2LibCoreSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
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
      | throwError "Array2 core API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkArray2CoreContract)
  "#check_array2_core_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_array2_core_contract [$ids:ident,*] => $expected:num) => do
      let names ← resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual ← apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "Array2 core API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "Array2 core declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"Array2 core API contract verified for {names.size} declarations"

#check Array2LibCoreSig
#check Array2LibCoreSig.canonical
#check store_array_rec_to_undef_array_rec
#check store_array_to_undef_array
#check store_undef_array_rec_split_to_missing_i
#check store_undef_array_split_to_missing_i
#check Array2Lib.row_addr
#check Array2Lib.row_store
#check Array2Lib.mixed_row_store
#check Array2Lib.undef_row_store
#check Array2Lib.full
#check Array2Lib.missing_i
#check Array2Lib.mixed_full
#check Array2Lib.mixed_missing_i
#check Array2Lib.undef_full
#check Array2Lib.undef_missing_i
#check Array2Lib.full_Zlength
#check Array2Lib.mixed_full_Zlength
#check Array2Lib.missing_i_Zlength
#check Array2Lib.mixed_missing_i_Zlength
#check Array2Lib.full_valid
#check Array2Lib.mixed_full_valid
#check Array2Lib.row_store_to_undef_row_store
#check Array2Lib.mixed_row_store_to_undef_row_store
#check Array2Lib.full_split_to_missing_i
#check Array2Lib.missing_i_merge_to_full
#check Array2Lib.mixed_full_split_to_mixed_missing_i
#check Array2Lib.mixed_missing_i_merge_to_mixed_full
#check Array2Lib.undef_full_split_to_undef_missing_i
#check Array2Lib.full_to_undef_full
#check Array2Lib.mixed_full_to_undef_full
#check Array2Lib.undef_full_valid

-- The 30-item manifest freezes names, complete types, binder order and visibility.
-- It also rejects dependencies outside the three expected Lean foundations.
#check_array2_core_contract [
  store_array_rec_to_undef_array_rec,
  store_array_to_undef_array,
  store_undef_array_rec_split_to_missing_i,
  store_undef_array_split_to_missing_i,
  Array2Lib.row_addr,
  Array2Lib.row_store,
  Array2Lib.mixed_row_store,
  Array2Lib.undef_row_store,
  Array2Lib.full,
  Array2Lib.missing_i,
  Array2Lib.mixed_full,
  Array2Lib.mixed_missing_i,
  Array2Lib.undef_full,
  Array2Lib.undef_missing_i,
  Array2Lib.full_Zlength,
  Array2Lib.mixed_full_Zlength,
  Array2Lib.missing_i_Zlength,
  Array2Lib.mixed_missing_i_Zlength,
  Array2Lib.full_valid,
  Array2Lib.mixed_full_valid,
  Array2Lib.row_store_to_undef_row_store,
  Array2Lib.mixed_row_store_to_undef_row_store,
  Array2Lib.full_split_to_missing_i,
  Array2Lib.missing_i_merge_to_full,
  Array2Lib.mixed_full_split_to_mixed_missing_i,
  Array2Lib.mixed_missing_i_merge_to_mixed_full,
  Array2Lib.undef_full_split_to_undef_missing_i,
  Array2Lib.full_to_undef_full,
  Array2Lib.mixed_full_to_undef_full,
  Array2Lib.undef_full_valid
] => 14583817559535070111

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}
variable (ES : ELEMENT_STORE CRules DePredSig SLibSig)

example (x m i : Int) :
    Array2Lib.row_addr ES x m i = x + i * m * ES.sizeA := rfl

example (x m : Int) :
    Array2Lib.undef_full ES x 0 m =
      CRules.andp (CRules.coq_prop ((0 : Int) = 0)) CRules.emp := rfl

example (x m : Int) :
    Array2Lib.undef_full ES x (-1) m =
      CRules.andp (CRules.coq_prop ((0 : Int) = -1)) CRules.emp := rfl

example (x i m : Int) :
    Array2Lib.undef_missing_i ES x i 3 1 m =
      store_undef_array_missing_i_rec CRules
        (Array2Lib.undef_row_store ES m) x i 3 1 0 := rfl

example (x i n m : Int) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (Array2Lib.undef_full ES x n m)
      (CRules.sepcon
        (ArrayLib.undef_full ES (Array2Lib.row_addr ES x m i) m)
        (Array2Lib.undef_missing_i ES x i 0 n m)) :=
  Array2Lib.undef_full_split_to_undef_missing_i ES x i n m h

example (x m : Int) :
    CRules.derivable1 (Array2Lib.undef_full ES x 3 m)
      (CRules.sepcon
        (ArrayLib.undef_full ES (Array2Lib.row_addr ES x m 0) m)
        (Array2Lib.undef_missing_i ES x 0 0 3 m)) :=
  Array2Lib.undef_full_split_to_undef_missing_i ES x 0 3 m (by omega)

example (x m : Int) :
    CRules.derivable1 (Array2Lib.undef_full ES x 3 m)
      (CRules.sepcon
        (ArrayLib.undef_full ES (Array2Lib.row_addr ES x m 2) m)
        (Array2Lib.undef_missing_i ES x 2 0 3 m)) :=
  Array2Lib.undef_full_split_to_undef_missing_i ES x 2 3 m (by omega)

example (x m : Int) (rows : List (List (Option ES.A))) :
    CRules.derivable1 (Array2Lib.mixed_full ES x 3 m rows)
      (CRules.sepcon
        (ArrayLib.mixed_full ES (Array2Lib.row_addr ES x m 0) m
          (Znth 0 rows []))
        (Array2Lib.mixed_missing_i ES x 0 0 3 m rows)) :=
  Array2Lib.mixed_full_split_to_mixed_missing_i ES x 0 3 m rows (by omega)

example (x m : Int) (rows : List (List (Option ES.A)))
    (row : List (Option ES.A)) :
    CRules.derivable1
      (CRules.sepcon
        (ArrayLib.mixed_full ES (Array2Lib.row_addr ES x m 2) m row)
        (Array2Lib.mixed_missing_i ES x 2 0 3 m rows))
      (Array2Lib.mixed_full ES x 3 m (replace_Znth 2 row rows)) :=
  Array2Lib.mixed_missing_i_merge_to_mixed_full ES x 2 3 m rows row (by omega)

example (x i n m : Int) (rows : List (List ES.A)) (row : List ES.A)
    (h : 0 <= i ∧ i < n) :
    CRules.derivable1
      (CRules.sepcon
        (ArrayLib.full ES (Array2Lib.row_addr ES x m i) m row)
        (Array2Lib.missing_i ES x i 0 n m rows))
      (Array2Lib.full ES x n m (replace_Znth i row rows)) :=
  Array2Lib.missing_i_merge_to_full ES x i n m rows row h

end

#print axioms SimpleC.SL.Array2LibCore.Array2LibCoreSig.store_array_to_undef_array
#print axioms SimpleC.SL.Array2LibCore.Array2LibCoreSig.store_undef_array_rec_split_to_missing_i
#print axioms SimpleC.SL.Array2LibCore.Array2LibCoreSig.Array2Lib.full_split_to_missing_i
#print axioms SimpleC.SL.Array2LibCore.Array2LibCoreSig.Array2Lib.missing_i_merge_to_full
#print axioms SimpleC.SL.Array2LibCore.Array2LibCoreSig.Array2Lib.undef_full_valid

end Array2LibCoreTests
