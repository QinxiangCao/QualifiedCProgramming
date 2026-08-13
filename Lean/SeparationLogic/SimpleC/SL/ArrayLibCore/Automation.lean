import SimpleC.SL.ArrayLibCore.Basic
import Lean.Elab.Tactic

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open Unifysl.LogicGenerator.demo932

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : SimpleC.SL.StoreAux.StoreLibSig CRules DePredSig}

private theorem undef_full_unfold_auto
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (h : n >= 0) :
    CRules.logic_equiv (undef_full ES x (n + 1))
      (CRules.sepcon (ES.undefstoreA x 0) (undef_seg ES x 1 (n + 1))) :=
  undef_full_unfold ES x n [] h

private theorem full_shape_unfold_auto
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (h : n >= 0) :
    CRules.logic_equiv (full_shape ES x (n + 1))
      (CRules.exp ES.A fun a =>
        CRules.sepcon (ES.storeA x 0 a) (seg_shape ES x 1 (n + 1))) :=
  full_shape_unfold ES x n [] h

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

syntax "ArraySimplify" : tactic

namespace SimpleC.SL.ArrayLibCore.ArraySimplifyImpl

open Lean Meta Elab Tactic

private inductive Shape where
  | emptyList
  | consList
  | sameLastTwo
  | zeroLast
  | addOneLast

private structure Branch where
  head : Name
  shape : Shape
  theoremName : Name
  explicitArity : Nat

private def ofNatValue? (expr : Expr) : Option Nat :=
  if expr.getAppFn.isConstOf ``OfNat.ofNat then
    let args := expr.getAppArgs
    if args.size >= 2 then args[args.size - 2]!.rawNatLit? else none
  else
    none

private def matchesShape (expr : Expr) (name : Name) (shape : Shape) : Bool :=
  if !expr.getAppFn.isConstOf name then
    false
  else
    let args := expr.getAppArgs
    if args.isEmpty then
      false
    else
      let last := args[args.size - 1]!
      match shape with
      | .emptyList => last.getAppFn.isConstOf ``List.nil
      | .consList => last.getAppFn.isConstOf ``List.cons
      | .sameLastTwo =>
          args.size >= 2 && args[args.size - 2]! == last
      | .zeroLast => ofNatValue? last == some 0
      | .addOneLast =>
          last.getAppFn.isConstOf ``HAdd.hAdd &&
            let addArgs := last.getAppArgs
            !addArgs.isEmpty && ofNatValue? addArgs[addArgs.size - 1]! == some 1

private def firstSome {α : Type} : List (MetaM (Option α)) -> MetaM (Option α)
  | [] => pure none
  | action :: rest => do
      match ← action with
      | some value => pure (some value)
      | none => firstSome rest

private partial def findMatch?
    (target : Expr) (name : Name) (shape : Shape) : MetaM (Option Expr) := do
  let target ←
    match ← withTransparency .reducible <| unfoldDefinition? target with
    | some unfolded => pure unfolded
    | none => pure target
  if matchesShape target name shape then
    pure (some target)
  else
    match target with
    | .app fn arg =>
        firstSome [findMatch? fn name shape, findMatch? arg name shape]
    | .lam _ type body _ | .forallE _ type body _ =>
        firstSome [findMatch? type name shape, findMatch? body name shape]
    | .letE _ type value body _ =>
        firstSome [findMatch? type name shape, findMatch? value name shape,
          findMatch? body name shape]
    | .mdata _ body | .proj _ _ body => findMatch? body name shape
    | _ => pure none

private def explicitArgs (expr : Expr) (arity : Nat) : Array Expr :=
  let args := expr.getAppArgs
  args.extract (args.size - arity) args.size

private def buildRule (branch : Branch) (matched : Expr) : MetaM Expr := do
  if matched.hasLooseBVars then
    return ← mkConstWithFreshMVarLevels branch.theoremName
  let args := explicitArgs matched branch.explicitArity
  let last := args[args.size - 1]!
  let theoremArgs := match branch.shape with
    | .emptyList | .sameLastTwo | .zeroLast => args.extract 0 (args.size - 1)
    | .consList =>
        let listArgs := last.getAppArgs
        (args.extract 0 (args.size - 1)).push
          listArgs[listArgs.size - 1]! |>.push listArgs[listArgs.size - 2]!
    | .addOneLast =>
        let addArgs := last.getAppArgs
        (args.extract 0 (args.size - 1)).push addArgs[addArgs.size - 2]!
  mkAppM branch.theoremName theoremArgs

private def tryRewrite (rule : Expr) : TacticM Bool := do
  let saved <- saveState
  try
    AUXLib.SetoidRewrite.rewriteTargetOnce rule
    return true
  catch _ =>
    restoreState saved
    return false

private partial def run : TacticM Unit := do
  let goals <- getGoals
  if goals.isEmpty then
    return
  let goal := goals[0]!
  let target <- instantiateMVars (← goal.getType)
  let branches : Array Branch := #[
    ⟨``seg, .emptyList, ``seg_empty, 5⟩,
    ⟨``mixed_seg, .emptyList, ``mixed_seg_empty, 5⟩,
    ⟨``undef_seg, .sameLastTwo, ``undef_seg_empty, 4⟩,
    ⟨``seg_shape, .sameLastTwo, ``seg_shape_empty, 4⟩,
    ⟨``seg, .consList, ``seg_unfold, 5⟩,
    ⟨``mixed_seg, .consList, ``mixed_seg_unfold, 5⟩,
    ⟨``missing_i, .emptyList, ``missing_i_empty, 6⟩,
    ⟨``mixed_missing_i, .emptyList, ``mixed_missing_i_empty, 6⟩,
    ⟨``undef_missing_i, .sameLastTwo, ``undef_missing_i_empty, 5⟩,
    ⟨``missing_i_shape, .sameLastTwo, ``missing_i_shape_empty, 5⟩,
    ⟨``missing_i, .consList, ``missing_i_unfold, 6⟩,
    ⟨``mixed_missing_i, .consList, ``mixed_missing_i_unfold, 6⟩,
    ⟨``full, .emptyList, ``full_empty, 4⟩,
    ⟨``mixed_full, .emptyList, ``mixed_full_empty, 4⟩,
    ⟨``undef_full, .zeroLast, ``undef_full_empty, 3⟩,
    ⟨``full_shape, .zeroLast, ``full_shape_empty, 3⟩,
    ⟨``full, .consList, ``full_unfold, 4⟩,
    ⟨``mixed_full, .consList, ``mixed_full_unfold, 4⟩,
    ⟨``undef_full, .addOneLast, ``undef_full_unfold_auto, 3⟩,
    ⟨``full_shape, .addOneLast, ``full_shape_unfold_auto, 3⟩
  ]
  for branch in branches do
    if let some matched ← findMatch? target branch.head branch.shape then
      let rule ← buildRule branch matched
      if ← tryRewrite rule then
        run
        return

end SimpleC.SL.ArrayLibCore.ArraySimplifyImpl

elab "ArraySimplify" : tactic =>
  SimpleC.SL.ArrayLibCore.ArraySimplifyImpl.run
