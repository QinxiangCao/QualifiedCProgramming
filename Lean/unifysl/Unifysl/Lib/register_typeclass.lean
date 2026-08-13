import Lean

open Lean Meta Elab Term Tactic

namespace Unifysl

class RegisterClass (Kind : Type u) {A : outParam (Type v)} (a : outParam A)
    (n : Nat) : Type (max u v) where

namespace RegisterTypeclass

private def betaZetaReduce (e : Expr) : MetaM Expr := do
  let e <- Core.betaReduce e
  zetaReduce e

private def mkRegisterClassType (kind : Expr) (A : Expr) (a : Expr) (n : Expr)
    (u v : Level) : Expr :=
  mkAppN (mkConst ``RegisterClass [u, v]) #[kind, A, a, n]

private def elabGetNth (kindStx nStx : Syntax) (reduceResult : Bool) : TermElabM Expr := do
  let u <- mkFreshLevelMVar
  let v <- mkFreshLevelMVar
  let kind <- elabTerm kindStx (mkSort (.succ u))
  let n <- elabTerm nStx (mkConst ``Nat)
  let A <- mkFreshExprMVar (mkSort (.succ v))
  let a <- mkFreshExprMVar A
  let registerClassType := mkRegisterClassType kind A a n u v
  discard <| synthInstance registerClassType
  let a <- instantiateMVars a
  if a.hasExprMVar then
    throwError "get_nth failed to infer a registered value for index {nStx}"
  if reduceResult then
    betaZetaReduce a
  else
    pure a

partial def rec_from_n (n : Nat) (tac : Nat -> TacticM Unit) : TacticM Unit := do
  let saved <- saveState
  try
    tac n
    rec_from_n (n + 1) tac
  catch _ =>
    restoreState saved

partial def applyInstanceArguments (e : Expr) : TacticM Expr := do
  let e <- instantiateMVars e
  let type <- inferType e
  let type <- instantiateMVars type
  let type <- whnf type
  match type with
  | Expr.forallE _ argType _ _ =>
      let argType <- instantiateMVars argType
      let arg <- try
        synthInstance argType
      catch _ =>
        throwError "pose_proof_instance_as failed: remaining argument cannot be synthesized by instance search{indentExpr argType}"
      let e <- betaZetaReduce (mkApp e arg)
      applyInstanceArguments e
  | _ =>
      pure e

def evalPoseProofInstanceAs (proofStx : Syntax) (name : Name) : TacticM Unit := withMainContext do
  let proof <- Tactic.elabTerm proofStx none
  let proof <- applyInstanceArguments proof
  let proof <- instantiateMVars proof
  let type <- inferType proof
  let type <- instantiateMVars type
  if proof.hasExprMVar || type.hasExprMVar then
    throwError "pose_proof_instance_as produced unresolved metavariables"
  let goal <- getMainGoal
  let (_, goal) <- goal.note name proof (some type)
  replaceMainGoal [goal]

end RegisterTypeclass

syntax (name := getNthPrime) "get_nth' " term:arg term:arg : term
syntax (name := getNth) "get_nth " term:arg term:arg : term

@[term_elab getNthPrime] def elabGetNthPrime : TermElab := fun stx _ => do
  match stx with
  | `(get_nth' $kindStx:term $nStx:term) =>
      RegisterTypeclass.elabGetNth kindStx nStx false
  | _ =>
      throwUnsupportedSyntax

@[term_elab getNth] def elabGetNth : TermElab := fun stx _ => do
  match stx with
  | `(get_nth $kindStx:term $nStx:term) =>
      RegisterTypeclass.elabGetNth kindStx nStx true
  | _ =>
      throwUnsupportedSyntax

syntax "pose_proof_instance_as " ident ident : tactic
syntax "pose_proof_instance_as " term " as " ident : tactic

elab "pose_proof_instance_as " proofStx:ident nameStx:ident : tactic =>
  RegisterTypeclass.evalPoseProofInstanceAs proofStx nameStx.getId

elab "pose_proof_instance_as " proofStx:term " as " nameStx:ident : tactic =>
  RegisterTypeclass.evalPoseProofInstanceAs proofStx nameStx.getId

namespace RegisterTypeclassTest

inductive TestKind : Type where

instance : RegisterClass TestKind (A := Nat) 37 0 := {}
instance : RegisterClass TestKind (A := Bool) true 1 := {}

example : (get_nth TestKind 0) = (37 : Nat) := rfl
example : (get_nth' TestKind 1) = true := rfl

class TestClass : Prop where
  trivial_proof : True

instance : TestClass where
  trivial_proof := True.intro

def test_instance_function (_ : TestClass) : True :=
  TestClass.trivial_proof

example : True := by
  pose_proof_instance_as test_instance_function h
  exact h

example : True := by
  run_tac
    RegisterTypeclass.rec_from_n 0 fun n => do
      if n == 0 then
        let goal <- getMainGoal
        let (_, goal) <- goal.note `h0 (mkConst ``True.intro) (some (mkConst ``True))
        replaceMainGoal [goal]
      else if n == 1 then
        let goal <- getMainGoal
        let (_, goal) <- goal.note `h1 (mkConst ``True.intro) (some (mkConst ``True))
        replaceMainGoal [goal]
      else
        throwError "stop"
  exact h1

end RegisterTypeclassTest

end Unifysl
