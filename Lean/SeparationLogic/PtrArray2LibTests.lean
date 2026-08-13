import SimpleC.SL.PtrArray2Lib
import Lean.Util.CollectAxioms

namespace PtrArray2LibTests

open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.PtrArray2Lib
open SimpleC.SL.PtrArray2Lib.PtrArray2LibSig
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "PtrArray2 facade declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkPtrArray2FacadeContract)
  "#check_ptr_array2_facade_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_ptr_array2_facade_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "PtrArray2 facade API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[
        ``propext,
        ``Classical.choice,
        ``Quot.sound,
        ``SimpleC.SL.CNotation.sizeof_front_end_type,
        ``SimpleC.SL.CNotation.sizeof_char,
        ``SimpleC.SL.CNotation.sizeof_uchar,
        ``SimpleC.SL.CNotation.sizeof_short,
        ``SimpleC.SL.CNotation.sizeof_ushort,
        ``SimpleC.SL.CNotation.sizeof_int,
        ``SimpleC.SL.CNotation.sizeof_uint,
        ``SimpleC.SL.CNotation.sizeof_int64,
        ``SimpleC.SL.CNotation.sizeof_uint64,
        ``SimpleC.SL.CNotation.sizeof_ptr]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "PtrArray2 facade declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"PtrArray2 facade API contract verified for {names.size} declarations"

#check PtrArray2LibSig
#check PtrArray2LibSig.canonical
#check PtrArray2Facade
#check CharPtrArray2
#check UCharPtrArray2
#check ShortPtrArray2
#check UShortPtrArray2
#check IntPtrArray2
#check UIntPtrArray2
#check Int64PtrArray2
#check UInt64PtrArray2
#check PtrPtrArray2
#check PtrArray2Facade.remove_Znth
#check PtrArray2Facade.replace_nth_decomp
#check PtrArray2Facade.replace_Znth_decomp
#check PtrArray2Facade.Znth_combine
#check PtrArray2Facade.combine_replace_Znth_r
#check PtrArray2Facade.single_to_iter_sepcon
#check PtrArray2Facade.iter_sepcon_split_remove_Znth
#check PtrArray2Facade.iter_sepcon_merge_remove_Znth
#check PtrArray2Facade.row_block
#check PtrArray2Facade.mixed_row_block
#check PtrArray2Facade.row_blocks
#check PtrArray2Facade.mixed_row_blocks
#check PtrArray2Facade.row_blocks_missing_i
#check PtrArray2Facade.mixed_row_blocks_missing_i
#check PtrArray2Facade.full
#check PtrArray2Facade.missing_i
#check PtrArray2Facade.mixed_full
#check PtrArray2Facade.mixed_missing_i
#check PtrArray2Facade.undef_full
#check PtrArray2Facade.full_Zlength
#check PtrArray2Facade.mixed_full_Zlength
#check PtrArray2Facade.undef_full_valid
#check PtrArray2Facade.Zlength_combine_eq
#check PtrArray2Facade.row_blocks_split_to_missing_i
#check PtrArray2Facade.mixed_row_blocks_split_to_missing_i
#check PtrArray2Facade.row_blocks_missing_i_merge_to_full
#check PtrArray2Facade.mixed_row_blocks_missing_i_merge_to_full
#check PtrArray2Facade.full_split_to_missing_i
#check PtrArray2Facade.missing_i_merge_to_full
#check PtrArray2Facade.mixed_full_split_to_mixed_missing_i
#check PtrArray2Facade.mixed_missing_i_merge_to_mixed_full

#check_ptr_array2_facade_contract [
  PtrArray2LibSig,
  PtrArray2LibSig.canonical,
  PtrArray2Facade,
  CharPtrArray2,
  UCharPtrArray2,
  ShortPtrArray2,
  UShortPtrArray2,
  IntPtrArray2,
  UIntPtrArray2,
  Int64PtrArray2,
  UInt64PtrArray2,
  PtrPtrArray2,
  PtrArray2Facade.remove_Znth,
  PtrArray2Facade.replace_nth_decomp,
  PtrArray2Facade.replace_Znth_decomp,
  PtrArray2Facade.Znth_combine,
  PtrArray2Facade.combine_replace_Znth_r,
  PtrArray2Facade.single_to_iter_sepcon,
  PtrArray2Facade.iter_sepcon_split_remove_Znth,
  PtrArray2Facade.iter_sepcon_merge_remove_Znth,
  PtrArray2Facade.row_block,
  PtrArray2Facade.mixed_row_block,
  PtrArray2Facade.row_blocks,
  PtrArray2Facade.mixed_row_blocks,
  PtrArray2Facade.row_blocks_missing_i,
  PtrArray2Facade.mixed_row_blocks_missing_i,
  PtrArray2Facade.full,
  PtrArray2Facade.missing_i,
  PtrArray2Facade.mixed_full,
  PtrArray2Facade.mixed_missing_i,
  PtrArray2Facade.undef_full,
  PtrArray2Facade.full_Zlength,
  PtrArray2Facade.mixed_full_Zlength,
  PtrArray2Facade.undef_full_valid,
  PtrArray2Facade.Zlength_combine_eq,
  PtrArray2Facade.row_blocks_split_to_missing_i,
  PtrArray2Facade.mixed_row_blocks_split_to_missing_i,
  PtrArray2Facade.row_blocks_missing_i_merge_to_full,
  PtrArray2Facade.mixed_row_blocks_missing_i_merge_to_full,
  PtrArray2Facade.full_split_to_missing_i,
  PtrArray2Facade.missing_i_merge_to_full,
  PtrArray2Facade.mixed_full_split_to_mixed_missing_i,
  PtrArray2Facade.mixed_missing_i_merge_to_mixed_full
] => 5106156880368916753

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}

example : (CharPtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (UCharPtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (ShortPtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (UShortPtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (IntPtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (UIntPtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (Int64PtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (UInt64PtrArray2 CRules DePredSig SLibSig).A = Int := rfl
example : (PtrPtrArray2 CRules DePredSig SLibSig).A = Int := rfl

example : (CharPtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreCharAsElement CRules DePredSig SLibSig := rfl
example : (UCharPtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreUCharAsElement CRules DePredSig SLibSig := rfl
example : (ShortPtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreShortAsElement CRules DePredSig SLibSig := rfl
example : (UShortPtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreUShortAsElement CRules DePredSig SLibSig := rfl
example : (IntPtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreIntAsElement CRules DePredSig SLibSig := rfl
example : (UIntPtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreUIntAsElement CRules DePredSig SLibSig := rfl
example : (Int64PtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreInt64AsElement CRules DePredSig SLibSig := rfl
example : (UInt64PtrArray2 CRules DePredSig SLibSig).elementStore =
    StoreUInt64AsElement CRules DePredSig SLibSig := rfl
example : (PtrPtrArray2 CRules DePredSig SLibSig).elementStore =
    StorePtrAsElement CRules DePredSig SLibSig := rfl

example : (IntPtrArray2 CRules DePredSig SLibSig).remove_Znth (-1) [1, 2, 3] = [2, 3] := by
  rfl

#check (CharPtrArray2 CRules DePredSig SLibSig).full
#check (UCharPtrArray2 CRules DePredSig SLibSig).missing_i
#check (ShortPtrArray2 CRules DePredSig SLibSig).mixed_full
#check (UShortPtrArray2 CRules DePredSig SLibSig).undef_full
#check (IntPtrArray2 CRules DePredSig SLibSig).full_split_to_missing_i
#check (UIntPtrArray2 CRules DePredSig SLibSig).missing_i_merge_to_full
#check (Int64PtrArray2 CRules DePredSig SLibSig).row_blocks_split_to_missing_i
#check (UInt64PtrArray2 CRules DePredSig SLibSig).mixed_row_blocks_missing_i_merge_to_full
#check (PtrPtrArray2 CRules DePredSig SLibSig).undef_full_valid

end

#print axioms IntPtrArray2
#print axioms PtrPtrArray2

end PtrArray2LibTests
