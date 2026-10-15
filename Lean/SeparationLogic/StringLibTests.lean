import SimpleC.SL.StringLib
import SimpleC.SL.Assertion
import Lean.Util.CollectAxioms

namespace StringLibTests

open SimpleC.SL.CArch
open AUXLib
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.Assertion
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.DerivedPredSigCompat
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open SimpleC.SL.StringLib
open SimpleC.SL.StringLib.StringLibSig
open Unifysl.LogicGenerator.demo932

open Lean Elab Command

local instance : SacContext := ⟨SL⟩

private abbrev TestDerived : DerivedPredSigCompat.Sig SL :=
  DerivedPredSigCompat.canonical SL

private abbrev TestStore : StoreLibSigCompat SL TestDerived :=
  StoreLibSigCompat.canonical SL TestDerived

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "StringLib API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkStringLibContract)
  "#check_stringlib_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_stringlib_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "StringLib API type hash changed: expected {expected}, got {actual}"
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
            throwError "StringLib declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"StringLib API contract verified for {names.size} declarations"

#check CoqAscii
#check CoqString
#check CoqString.ofString
#check StringLibSig
#check AsciiToZ
#check ZToAscii
#check string_length
#check c_string
#check valid_char
#check valid_string
#check StringLength
#check StringToList_nat
#check StringToList
#check ListToString
#check ZToAscii_AsciiToZ
#check ListToString_StringToList_nat_full
#check ListToString_StringToList
#check valid_stringLit
#check store_string
#check store_stringLit
#check StringLibSig.GlobalStrings
#check StringLibSig.GlobalStrings_missing
#check StringLibSig.GlobalStrings_split
#check StringLibSig.GlobalStrings_merge
#check StringLibSig.GlobalStrings_missing_split
#check StringLibSig.GlobalStrings_missing_merge
#check StringLibSig.GlobalStrings_split_existing
#check c_string_Zlength
#check StringToList_nat_length
#check StringToList_length
#check StringToList_c_length
#check store_string_length
#check store_stringLit_length
#check store_string_split_to_missing_i
#check store_stringLit_split_to_missing_i
#check AsciiToZ_range

#check_stringlib_contract [
  CoqAscii,
  CoqString,
  CoqString.ofString,
  StringLibSig,
  AsciiToZ,
  ZToAscii,
  string_length,
  c_string,
  valid_char,
  valid_string,
  StringLength,
  StringToList_nat,
  StringToList,
  ListToString,
  ZToAscii_AsciiToZ,
  ListToString_StringToList_nat_full,
  ListToString_StringToList,
  valid_stringLit,
  store_string,
  store_stringLit,
  StringLibSig.GlobalStrings,
  StringLibSig.GlobalStrings_missing,
  StringLibSig.GlobalStrings_split,
  StringLibSig.GlobalStrings_merge,
  StringLibSig.GlobalStrings_missing_split,
  StringLibSig.GlobalStrings_missing_merge,
  StringLibSig.GlobalStrings_split_existing,
  c_string_Zlength,
  StringToList_nat_length,
  StringToList_length,
  StringToList_c_length,
  store_string_length,
  store_stringLit_length,
  store_string_split_to_missing_i,
  store_stringLit_split_to_missing_i,
  AsciiToZ_range
] => 14899891327909765336

example (c : CoqAscii) : AsciiToZ c = Int.ofNat c.toNat := rfl
example (z : Int) : ZToAscii z = UInt8.ofNat (z % 256).toNat := rfl
example (s : List Int) : string_length s = Zlength s := rfl
example (s : List Int) : c_string s = s ++ [0] := rfl
example (z : Int) : valid_char z = (0 < z ∧ z < 256) := rfl
example (s : List Int) : valid_string s = Forall valid_char s := rfl
example (s : CoqString) : StringLength s = Int.ofNat s.length := rfl
example (s : CoqString) (n : Int) :
    StringToList s n = StringToList_nat s n.toNat := rfl
example : ListToString [] = [] := rfl
example (c : Int) (s : List Int) :
    ListToString (c :: s) = ZToAscii c :: ListToString s := rfl
example (s : CoqString) :
    valid_stringLit s = valid_string (StringToList s (StringLength s)) := rfl

example : ZToAscii (-1) = (255 : UInt8) := by decide
example : ZToAscii 0 = (0 : UInt8) := by decide
example : ZToAscii 255 = (255 : UInt8) := by decide
example : ZToAscii 256 = (0 : UInt8) := by decide
example : ZToAscii 257 = (1 : UInt8) := by decide

example : CoqString.ofString "abc" = [97, 98, 99] := by native_decide
example : CoqString.ofString "é" = [195, 169] := by native_decide

example : StringToList [] 3 = [0, 0, 0] := by decide
example : StringToList [65, 66, 67] 2 = [65, 66] := by decide
example : StringToList [65] 3 = [65, 0, 0] := by decide
example : StringToList [65] (-3) = [] := by decide
example : c_string [65, 66] = [65, 66, 0] := by decide
example (c : CoqAscii) : ZToAscii (AsciiToZ c) = c :=
  ZToAscii_AsciiToZ c

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSigCompat.Sig CRules}
variable {SLibSig : StoreLibSigCompat CRules DePredSig}
variable {ALibSig : ArrayLibSig Arch32 BigEndian CRules DePredSig SLibSig}

example (x : addr) (s : List Int) :
    store_string Arch32 BigEndian CRules DePredSig SLibSig x s =
      CRules.andp (CRules.coq_prop (valid_string s))
        ((CharArray Arch32 BigEndian CRules DePredSig SLibSig).full
          x (string_length s + 1) (c_string s)) := rfl

example (x : addr) (s : CoqString) :
    store_stringLit Arch32 BigEndian CRules DePredSig SLibSig x s =
      CRules.andp (CRules.coq_prop (valid_stringLit s))
        ((CharArray Arch32 BigEndian CRules DePredSig SLibSig).full
          x (StringLength s + 1) (StringToList s (StringLength s + 1))) := rfl

example (x : addr) (s : List Int) :
    CRules.derivable1 (store_string Arch32 BigEndian CRules DePredSig SLibSig x s)
      (CRules.coq_prop (Zlength (c_string s) = string_length s + 1)) :=
  store_string_length Arch32 BigEndian CRules DePredSig SLibSig x s

example (x i : addr) (s : List Int) (hi : 0 <= i ∧ i < string_length s + 1) :
    CRules.derivable1 (store_string Arch32 BigEndian CRules DePredSig SLibSig x s)
      (CRules.sepcon
        (SimpleC.SL.CommonAssertion.DerivedPredSig.store_char Arch32 CRules
          (x + i * SimpleC.SL.CNotation.CNotationSig.sizeof_front_end_type Arch32
            SimpleC.SL.CNotation.FET_char)
          (Znth i (c_string s) 0))
        ((CharArray Arch32 BigEndian CRules DePredSig SLibSig).missing_i
          x i 0 (string_length s + 1) (c_string s))) :=
  store_string_split_to_missing_i Arch32 BigEndian CRules DePredSig SLibSig x i s hi

example (x i : addr) (s : CoqString) (hi : 0 <= i ∧ i < StringLength s + 1) :
    CRules.derivable1 (store_stringLit Arch32 BigEndian CRules DePredSig SLibSig x s)
      (CRules.sepcon
        (SimpleC.SL.CommonAssertion.DerivedPredSig.store_char Arch32 CRules
          (x + i * SimpleC.SL.CNotation.CNotationSig.sizeof_front_end_type Arch32
            SimpleC.SL.CNotation.FET_char)
          (Znth i (StringToList s (StringLength s + 1)) 0))
        ((CharArray Arch32 BigEndian CRules DePredSig SLibSig).missing_i
          x i 0 (StringLength s + 1)
          (StringToList s (StringLength s + 1)))) :=
  store_stringLit_split_to_missing_i Arch32 BigEndian CRules DePredSig SLibSig x i s hi

variable (API : StringLibSig Arch32 BigEndian CRules DePredSig SLibSig ALibSig)
variable (LitMap : CoqString -> addr) (s : CoqString)

example : CRules.derivable1 (API.GlobalStrings LitMap)
    (CRules.sepcon (API.GlobalStrings_missing LitMap [s])
      (store_stringLit Arch32 BigEndian CRules DePredSig SLibSig (LitMap s) s)) :=
  API.GlobalStrings_split LitMap s

end

section SourceTactics

example (x : addr) (s : List Int) :
    SL.derivable1 (store_string Arch32 BigEndian SL TestDerived TestStore x s)
      (SL.coq_prop (Zlength (c_string s) = string_length s + 1)) := by
  unfold store_string
  entailer!
  all_goals exact c_string_Zlength s

example (x : addr) (s : CoqString) :
    SL.derivable1 (store_stringLit Arch32 BigEndian SL TestDerived TestStore x s)
      (SL.coq_prop
        (Zlength (StringToList s (StringLength s + 1)) =
          StringLength s + 1)) := by
  unfold store_stringLit
  entailer!
  all_goals exact StringToList_c_length s

example (x i : addr) (s : List Int) (hi : 0 <= i ∧ i < string_length s + 1) :
    SL.derivable1 (store_string Arch32 BigEndian SL TestDerived TestStore x s)
      (SL.sepcon
        (SimpleC.SL.CommonAssertion.DerivedPredSig.store_char Arch32 SL
          (x + i * SimpleC.SL.CNotation.CNotationSig.sizeof_front_end_type Arch32
            SimpleC.SL.CNotation.FET_char)
          (Znth i (c_string s) 0))
        ((CharArray Arch32 BigEndian SL TestDerived TestStore).missing_i
          x i 0 (string_length s + 1) (c_string s))) := by
  unfold store_string
  refine coq_prop_andp_left SL _ _ _ ?_
  intro _
  sep_apply ((CharArray Arch32 BigEndian SL TestDerived TestStore).full_split_to_missing_i
    x i (string_length s + 1) (c_string s) (0 : Int) hi)
  exact SL.toContext.derivable1_refl _

example (x i : addr) (s : CoqString) (hi : 0 <= i ∧ i < StringLength s + 1) :
    SL.derivable1 (store_stringLit Arch32 BigEndian SL TestDerived TestStore x s)
      (SL.sepcon
        (SimpleC.SL.CommonAssertion.DerivedPredSig.store_char Arch32 SL
          (x + i * SimpleC.SL.CNotation.CNotationSig.sizeof_front_end_type Arch32
            SimpleC.SL.CNotation.FET_char)
          (Znth i (StringToList s (StringLength s + 1)) 0))
        ((CharArray Arch32 BigEndian SL TestDerived TestStore).missing_i
          x i 0 (StringLength s + 1)
          (StringToList s (StringLength s + 1)))) := by
  unfold store_stringLit
  refine coq_prop_andp_left SL _ _ _ ?_
  intro _
  sep_apply ((CharArray Arch32 BigEndian SL TestDerived TestStore).full_split_to_missing_i
    x i (StringLength s + 1) (StringToList s (StringLength s + 1))
      (0 : Int) hi)
  exact SL.toContext.derivable1_refl _

end SourceTactics

#print axioms SimpleC.SL.StringLib.StringLibSig.ZToAscii_AsciiToZ
#print axioms SimpleC.SL.StringLib.StringLibSig.store_string_split_to_missing_i

end StringLibTests
