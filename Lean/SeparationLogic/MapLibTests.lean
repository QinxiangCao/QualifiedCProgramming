import SimpleC.SL.MapLib
import Lean.Util.CollectAxioms

namespace MapLibTests

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.MapLib
open SimpleC.SL.MapLib.MapLibSig
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
      | throwError "MapLib API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkMapLibContract)
  "#check_maplib_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_maplib_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "MapLib API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "MapLib declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"MapLib API contract verified for {names.size} declarations"

#check MapLibSig
#check MapLibSig.canonical
#check store_map
#check store_map_missing_i
#check store_map_split
#check store_map_merge
#check store_map_missing_equiv_store_map
#check store_map_equiv_store_map_missing
#check store_map_equiv
#check store_map_missing_i_equiv
#check store_map_empty

#check_maplib_contract [
  MapLibSig,
  MapLibSig.canonical,
  store_map,
  store_map_missing_i,
  store_map_split,
  store_map_merge,
  store_map_missing_equiv_store_map,
  store_map_equiv_store_map_missing,
  store_map_equiv,
  store_map_missing_i_equiv,
  store_map_empty
] => 2048639483385255554

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}
variable {A B : Type}
variable (P : A -> B -> CRules.expr)
variable (m : A -> Option B)

example : MapLibSig CRules DePredSig SLibSig :=
  MapLibSig.canonical CRules DePredSig SLibSig

example : store_map CRules P m =
    CRules.exp (List A) fun l =>
      CRules.andp
        (CRules.coq_prop (forall a, a ∈ l <-> exists b, m a = some b))
        (CRules.andp (CRules.coq_prop (NoDup l))
          (CRules.toContext.iter_sepcon
            (l.map fun a => match m a with
              | some b => P a b
              | none => CRules.emp))) := rfl

example (a : A) : store_map_missing_i CRules P m a =
    CRules.exp (List A) fun l =>
      CRules.andp
        (CRules.coq_prop
          (forall x, x ∈ l <-> (exists b, m x = some b) ∧ x ≠ a))
        (CRules.andp (CRules.coq_prop (NoDup l))
          (CRules.toContext.iter_sepcon
            (l.map fun x => match m x with
              | some b => P x b
              | none => CRules.emp))) := rfl

example (a : A) (b : B) (h : m a = some b) :
    CRules.derivable1 (store_map CRules P m)
      (CRules.sepcon (store_map_missing_i CRules P m a) (P a b)) :=
  store_map_split CRules P a b m h

example (a : A) (b : B) (h : m a = some b) :
    CRules.derivable1
      (CRules.sepcon (store_map_missing_i CRules P m a) (P a b))
      (store_map CRules P m) :=
  store_map_merge CRules P a b m h

example (a : A) (b : B) (h : m a = some b) :
    CRules.derivable1 (store_map CRules P m)
      (CRules.sepcon (store_map_missing_i CRules P m a) (P a b)) := by
  letI : SacContext := ⟨CRules⟩
  sep_apply (store_map_split CRules P a b m h)
  entailer!

example (a : A) (b : B) (h : m a = some b) :
    CRules.derivable1
      (CRules.sepcon (store_map_missing_i CRules P m a) (P a b))
      (store_map CRules P m) := by
  letI : SacContext := ⟨CRules⟩
  sep_apply (store_map_merge CRules P a b m h)
  entailer!

example (a : A) (h : m a = none) :
    CRules.logic_equiv (store_map_missing_i CRules P m a)
      (store_map CRules P m) :=
  ⟨store_map_missing_equiv_store_map CRules P m a h,
    store_map_equiv_store_map_missing CRules P m a h⟩

example : CRules.logic_equiv
    (store_map CRules P (fun _ => none)) CRules.emp := by
  apply store_map_empty CRules P (fun _ => none)
  · exact ⟨[], by simp, by simp⟩
  · intro a
    exact Or.inl rfl

example (a : A) : ¬ NoDup [a, a] := by simp

end

#print axioms store_map_split
#print axioms store_map_merge
#print axioms store_map_empty

end MapLibTests
