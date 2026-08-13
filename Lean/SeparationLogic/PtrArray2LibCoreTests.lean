import SimpleC.SL.PtrArray2LibCore
import Lean.Util.CollectAxioms

namespace PtrArray2LibCoreTests

open AUXLib
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.PtrArray2LibCore
open SimpleC.SL.PtrArray2LibCore.PtrArray2LibCoreSig
open SimpleC.SL.PtrArray2LibCore.PtrArray2LibCoreSig.PtrArray2Lib
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
      | throwError "PtrArray2 core declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkPtrArray2CoreContract)
  "#check_ptr_array2_core_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_ptr_array2_core_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "PtrArray2 core API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[
        ``propext,
        ``Classical.choice,
        ``Quot.sound,
        ``SimpleC.SL.CNotation.sizeof_front_end_type,
        ``SimpleC.SL.CNotation.sizeof_ptr]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "PtrArray2 core declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"PtrArray2 core API contract verified for {names.size} declarations"

#check PtrArray2LibCoreSig
#check PtrArray2LibCoreSig.canonical
#check remove_Znth
#check replace_nth_decomp
#check replace_Znth_decomp
#check Znth_combine
#check combine_replace_Znth_r
#check single_to_iter_sepcon
#check iter_sepcon_split_remove_Znth
#check iter_sepcon_merge_remove_Znth
#check row_block
#check mixed_row_block
#check row_blocks
#check mixed_row_blocks
#check row_blocks_missing_i
#check mixed_row_blocks_missing_i
#check full
#check missing_i
#check mixed_full
#check mixed_missing_i
#check undef_full
#check full_Zlength
#check mixed_full_Zlength
#check undef_full_valid
#check Zlength_combine_eq
#check row_blocks_split_to_missing_i
#check mixed_row_blocks_split_to_missing_i
#check row_blocks_missing_i_merge_to_full
#check mixed_row_blocks_missing_i_merge_to_full
#check full_split_to_missing_i
#check missing_i_merge_to_full
#check mixed_full_split_to_mixed_missing_i
#check mixed_missing_i_merge_to_mixed_full

#check_ptr_array2_core_contract [
  remove_Znth,
  replace_nth_decomp,
  replace_Znth_decomp,
  Znth_combine,
  combine_replace_Znth_r,
  single_to_iter_sepcon,
  iter_sepcon_split_remove_Znth,
  iter_sepcon_merge_remove_Znth,
  row_block,
  mixed_row_block,
  row_blocks,
  mixed_row_blocks,
  row_blocks_missing_i,
  mixed_row_blocks_missing_i,
  full,
  missing_i,
  mixed_full,
  mixed_missing_i,
  undef_full,
  full_Zlength,
  mixed_full_Zlength,
  undef_full_valid,
  Zlength_combine_eq,
  row_blocks_split_to_missing_i,
  mixed_row_blocks_split_to_missing_i,
  row_blocks_missing_i_merge_to_full,
  mixed_row_blocks_missing_i_merge_to_full,
  full_split_to_missing_i,
  missing_i_merge_to_full,
  mixed_full_split_to_mixed_missing_i,
  mixed_missing_i_merge_to_mixed_full
] => 16725104168956533196

example : remove_Znth (-3) [10, 20, 30] = [20, 30] := by native_decide
example : remove_Znth 0 [10, 20, 30] = [20, 30] := by native_decide
example : remove_Znth 2 [10, 20, 30] = [10, 20] := by native_decide
example : remove_Znth 8 [10, 20, 30] = [10, 20, 30] := by native_decide

example : replace_nth 0 [10, 20, 30] 7 =
    firstn 0 [10, 20, 30] ++ 7 :: skipn 1 [10, 20, 30] :=
  replace_nth_decomp 0 [10, 20, 30] 7 (by decide)

example : replace_nth 2 [10, 20, 30] 7 =
    firstn 2 [10, 20, 30] ++ 7 :: skipn 3 [10, 20, 30] :=
  replace_nth_decomp 2 [10, 20, 30] 7 (by decide)

example : Znth 0 (combine [1, 2] [10, 20]) (0, 0) =
    (Znth 0 [1, 2] 0, Znth 0 [10, 20] 0) :=
  Znth_combine 0 [1, 2] [10, 20] 0 0 (by native_decide) rfl

example : Znth 1 (combine [1, 2] [10, 20]) (0, 0) =
    (Znth 1 [1, 2] 0, Znth 1 [10, 20] 0) :=
  Znth_combine 1 [1, 2] [10, 20] 0 0 (by native_decide) rfl

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}
variable (ES : ELEMENT_STORE CRules DePredSig SLibSig)

example {B : Type} (i : Int) (l : List B) :
    remove_Znth i l = firstn i.toNat l ++ skipn i.toNat.succ l := rfl

example (pr : Int × List ES.A) :
    row_block ES pr = ArrayLib.full ES pr.1 (Zlength pr.2) pr.2 := rfl

example (pr : Int × List (Option ES.A)) :
    mixed_row_block ES pr =
      ArrayLib.mixed_full ES pr.1 (Zlength pr.2) pr.2 := rfl

example (rowPtrs : List Int) (rows : List (List ES.A)) :
    row_blocks ES rowPtrs rows =
      CRules.toContext.iter_sepcon
        ((combine rowPtrs rows).map (row_block ES)) := rfl

example (rowPtrs : List Int) (rows : List (List (Option ES.A))) :
    mixed_row_blocks ES rowPtrs rows =
      CRules.toContext.iter_sepcon
        ((combine rowPtrs rows).map (mixed_row_block ES)) := rfl

example (i : Int) (rowPtrs : List Int) (rows : List (List ES.A)) :
    row_blocks_missing_i ES i rowPtrs rows =
      CRules.toContext.iter_sepcon
        ((remove_Znth i (combine rowPtrs rows)).map (row_block ES)) := rfl

example (i : Int) (rowPtrs : List Int)
    (rows : List (List (Option ES.A))) :
    mixed_row_blocks_missing_i ES i rowPtrs rows =
      CRules.toContext.iter_sepcon
        ((remove_Znth i (combine rowPtrs rows)).map (mixed_row_block ES)) := rfl

example (x n : Int) (rows : List (List ES.A)) :
    full ES x n rows =
      CRules.exp (List Int) fun rowPtrs =>
        CRules.andp
          (CRules.coq_prop (Zlength rowPtrs = n ∧ Zlength rows = n))
          (CRules.sepcon
            ((PtrArray CRules DePredSig SLibSig).full x n rowPtrs)
            (row_blocks ES rowPtrs rows)) := rfl

example (x n i rowPtr : Int) (rows : List (List ES.A)) :
    missing_i ES x n i rowPtr rows =
      CRules.exp (List Int) fun rowPtrs =>
        CRules.andp
          (CRules.coq_prop
            (Zlength rowPtrs = n ∧ Zlength rows = n ∧
              rowPtr = Znth i rowPtrs 0))
          (CRules.sepcon
            ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n rowPtrs)
            (row_blocks_missing_i ES i rowPtrs rows)) := rfl

example (x n : Int) (rows : List (List (Option ES.A))) :
    mixed_full ES x n rows =
      CRules.exp (List Int) fun rowPtrs =>
        CRules.andp
          (CRules.coq_prop (Zlength rowPtrs = n ∧ Zlength rows = n))
          (CRules.sepcon
            ((PtrArray CRules DePredSig SLibSig).full x n rowPtrs)
            (mixed_row_blocks ES rowPtrs rows)) := rfl

example (x n i rowPtr : Int) (rows : List (List (Option ES.A))) :
    mixed_missing_i ES x n i rowPtr rows =
      CRules.exp (List Int) fun rowPtrs =>
        CRules.andp
          (CRules.coq_prop
            (Zlength rowPtrs = n ∧ Zlength rows = n ∧
              rowPtr = Znth i rowPtrs 0))
          (CRules.sepcon
            ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n rowPtrs)
            (mixed_row_blocks_missing_i ES i rowPtrs rows)) := rfl

example (x n : Int) :
    undef_full ES x n =
      (PtrArray CRules DePredSig SLibSig).undef_full x n := rfl

example {B : Type} (P : B -> CRules.expr) (i : Int) (l : List B) (d : B)
    (h : 0 <= i ∧ i < Zlength l) :
    CRules.derivable1 (CRules.toContext.iter_sepcon (l.map P))
      (CRules.sepcon (P (Znth i l d))
        (CRules.toContext.iter_sepcon ((remove_Znth i l).map P))) := by
  letI : SacContext := ⟨CRules⟩
  sep_apply (iter_sepcon_split_remove_Znth CRules P i l d h)
  entailer!

example (x : Int) (rows : List (List ES.A)) :
    CRules.derivable1 (full ES x 3 rows)
      (CRules.exp Int fun rowPtr =>
        CRules.sepcon
          (CRules.sepcon
            ((StorePtrAsElement CRules DePredSig SLibSig).storeA x 0 rowPtr)
            (ArrayLib.full ES rowPtr (Zlength (Znth 0 rows []))
              (Znth 0 rows [])))
          (missing_i ES x 3 0 rowPtr rows)) := by
  letI : SacContext := ⟨CRules⟩
  sep_apply (full_split_to_missing_i ES x 0 3 rows (by omega))
  entailer!

example (x rowPtr : Int) (rows : List (List ES.A)) (row : List ES.A) :
    CRules.derivable1
      (CRules.sepcon
        (CRules.sepcon
          ((StorePtrAsElement CRules DePredSig SLibSig).storeA x 2 rowPtr)
          (ArrayLib.full ES rowPtr (Zlength row) row))
        (missing_i ES x 3 2 rowPtr rows))
      (full ES x 3 (replace_Znth 2 row rows)) := by
  letI : SacContext := ⟨CRules⟩
  sep_apply (missing_i_merge_to_full ES x 2 3 rowPtr rows row (by omega))
  entailer!

example (x : Int) (rows : List (List (Option ES.A))) :
    CRules.derivable1 (mixed_full ES x 3 rows)
      (CRules.exp Int fun rowPtr =>
        CRules.sepcon
          (CRules.sepcon
            ((StorePtrAsElement CRules DePredSig SLibSig).storeA x 0 rowPtr)
            (ArrayLib.mixed_full ES rowPtr (Zlength (Znth 0 rows []))
              (Znth 0 rows [])))
          (mixed_missing_i ES x 3 0 rowPtr rows)) := by
  letI : SacContext := ⟨CRules⟩
  sep_apply (mixed_full_split_to_mixed_missing_i ES x 0 3 rows (by omega))
  entailer!

example (x rowPtr : Int) (rows : List (List (Option ES.A)))
    (row : List (Option ES.A)) :
    CRules.derivable1
      (CRules.sepcon
        (CRules.sepcon
          ((StorePtrAsElement CRules DePredSig SLibSig).storeA x 2 rowPtr)
          (ArrayLib.mixed_full ES rowPtr (Zlength row) row))
        (mixed_missing_i ES x 3 2 rowPtr rows))
      (mixed_full ES x 3 (replace_Znth 2 row rows)) := by
  letI : SacContext := ⟨CRules⟩
  sep_apply (mixed_missing_i_merge_to_mixed_full
    ES x 2 3 rowPtr rows row (by omega))
  entailer!

example (x : Int) :
    CRules.derivable1 (undef_full ES x (-1)) (CRules.coq_prop (0 <= (-1 : Int))) :=
  undef_full_valid ES x (-1)

end

#print axioms replace_Znth_decomp
#print axioms iter_sepcon_split_remove_Znth
#print axioms full_split_to_missing_i
#print axioms missing_i_merge_to_full

end PtrArray2LibCoreTests
