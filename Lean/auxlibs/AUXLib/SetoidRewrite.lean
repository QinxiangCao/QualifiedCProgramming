import AUXLib.Morphisms
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Rewrite
import Lean.Meta.Tactic.Replace

namespace AUXLib

theorem relation_symm {A : Sort u} {R : A -> A -> Prop} [Symmetric R]
    {x y : A} (h : R x y) : R y x :=
  Symmetric.symm x y h

class ProperFunction {A : Sort u} {B : Sort v} (RA : A -> A -> Prop)
    (f : A -> B) (RB : outParam (B -> B -> Prop)) : Prop where
  proper : respectful RA RB f f

instance (priority := low) properFunction_eq {A : Sort u} {B : Sort v}
    (f : A -> B) : ProperFunction Eq f Eq where
  proper _ _ h := congrArg f h

set_option synthInstance.checkSynthOrder false in
instance properFunction_of_proper {A : Sort u} {B : Sort v}
    {RA : A -> A -> Prop} {RB : B -> B -> Prop} (f : A -> B)
    [h : Proper (RA ==> RB) f] : ProperFunction RA f RB where
  proper := h.proper

instance (priority := low) properFunction_doubleFlip
    {A : Sort u} {B : Sort v} {RA : A -> A -> Prop} {RB : B -> B -> Prop}
    (f : A -> B) [h : ProperFunction RA f RB] :
    ProperFunction (flipRel (flipRel RA)) f (flipRel (flipRel RB)) where
  proper x y hxy := h.proper x y hxy

instance (priority := low) properFunction_flipDependentPointwise
    {A : Sort u} {B : A -> Sort v} {C : Sort w}
    {R : forall x, B x -> B x -> Prop} {S : C -> C -> Prop}
    (f : (forall x, B x) -> C)
    [h : ProperFunction (dependentPointwise R) f S] :
    ProperFunction
      (flipRel (dependentPointwise (fun x => flipRel (R x)))) f S where
  proper p q hpq := h.proper p q fun x => hpq x

namespace SetoidRewrite

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

private def isDefEqForRewrite (lhs rhs : Expr) : MetaM Bool :=
  withTransparency .instances <| isDefEq lhs rhs

private def isDefEqForValidation (lhs rhs : Expr) : MetaM Bool := do
  let saved ← saveState
  if ← isDefEqForRewrite lhs rhs then
    return true
  restoreState saved
  isDefEq lhs rhs

inductive Orientation where
  | forward
  | backward

private def Orientation.flip : Orientation -> Orientation
  | .forward => .backward
  | .backward => .forward

structure Result where
  newExpr : Expr
  relation : Expr
  proof : Expr
  orientation : Orientation
  sideGoals : Array MVarId := #[]

private def isBinderTraversalWrapper (expr : Expr) : Bool :=
  expr.getAppFn.isConstOf ``implication || expr.getAppFn.isConstOf ``forallBinder

private def rewriteMark : Name := `_auxlibSetoidRewriteDone

private def mkRelationType (type : Expr) : MetaM Expr := do
  let sort ← inferType type
  let .sort _ := sort | throwError "relation carrier is not a sort"
  return .forallE `_ type (.forallE `_ type (.sort .zero) .default) .default

private def relationParts (proof : Expr) : MetaM (Expr × Expr × Expr) := do
  let type ← instantiateMVars (← inferType proof)
  let (type, fn, args) ←
    if type.getAppArgs.size ≥ 2 then
      pure (type, type.getAppFn, type.getAppArgs)
    else
      let reduced ← whnf type
      pure (reduced, reduced.getAppFn, reduced.getAppArgs)
  unless args.size ≥ 2 do
    throwError "rewrite theorem does not conclude with a binary relation{indentExpr type}"
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  let relation := mkAppN fn (args.extract 0 (args.size - 2))
  return (relation, lhs, rhs)

private partial def instantiateRuleBinders (proof : Expr)
    (sideGoals : Array MVarId := #[]) : MetaM (Expr × Array MVarId) := do
  let type ← instantiateMVars (← inferType proof)
  -- Only declaration binders are instantiated here; reducing a relation such as
  -- `implication P Q` would incorrectly consume the proof of `P` as a rule argument.
  match type with
  | .forallE _ domain _ _ =>
      if ← isProp domain then
        let arg ← mkFreshExprSyntheticOpaqueMVar domain
        instantiateRuleBinders (mkApp proof arg) (sideGoals.push arg.mvarId!)
      else
        let arg ← mkFreshExprMVar domain
        instantiateRuleBinders (mkApp proof arg) sideGoals
  | _ => return (proof, sideGoals)

private def instantiateRule (proof : Expr) :
    MetaM (Expr × Expr × Expr × Expr × Array MVarId) := do
  let (proof, sideGoals) ← instantiateRuleBinders proof
  let (relation, lhs, rhs) ← relationParts proof
  return (proof, relation, lhs, rhs, sideGoals)

private structure InstantiatedRule where
  proof : Expr
  relation : Expr
  lhs : Expr
  rhs : Expr
  orientation : Orientation
  sideGoals : Array MVarId
  markReplacement : Bool

private def instantiateOrientedRule (rule : Expr) (symm : Bool)
    (markReplacement : Bool := false) : MetaM InstantiatedRule := do
  let (proof, relation, ruleLhs, ruleRhs, sideGoals) ← instantiateRule rule
  if symm then
    return {
      proof := proof
      relation := relation
      lhs := ruleRhs
      rhs := ruleLhs
      orientation := .backward
      sideGoals := sideGoals
      markReplacement
    }
  return {
    proof := proof
    relation := relation
    lhs := ruleLhs
    rhs := ruleRhs
    orientation := .forward
    sideGoals := sideGoals
    markReplacement
  }

private def liftArgumentWithRelation (f oldArg newArg : Expr)
    (child : Result) : MetaM Result := do
  let argumentType ← inferType oldArg
  let resultType ← inferType (mkApp f oldArg)
  let relationType ← mkRelationType resultType
  let outRelation ← mkFreshExprMVar relationType
  let u ← getLevel argumentType
  let v ← getLevel resultType
  let properType := mkAppN (mkConst ``ProperFunction [u, v])
    #[argumentType, resultType, child.relation, f, outRelation]
  let properInst ← synthInstance properType
  let properProof := mkAppN (mkConst ``ProperFunction.proper [u, v])
    #[argumentType, resultType, child.relation, f, outRelation, properInst]
  let (proofLhs, proofRhs) := match child.orientation with
    | .forward => (oldArg, newArg)
    | .backward => (newArg, oldArg)
  let proof := mkApp3 properProof proofLhs proofRhs child.proof
  return {
    newExpr := mkApp f newArg
    relation := ← instantiateMVars outRelation
    proof := ← instantiateMVars proof
    orientation := child.orientation
    sideGoals := child.sideGoals
  }

private def liftArgument (f oldArg newArg : Expr) (child : Result) : MetaM Result := do
  let saved ← saveState
  try
    liftArgumentWithRelation f oldArg newArg child
  catch _ =>
    restoreState saved
    let flippedRelation ← mkAppM ``flipRel #[child.relation]
    liftArgumentWithRelation f oldArg newArg {
      child with
        relation := flippedRelation
        orientation := child.orientation.flip
    }

private def liftFunction (child : Result) (arg : Expr) : MetaM Result := do
  let fnType ← whnf (← inferType child.newExpr)
  let .forallE _ domain _ _ := fnType
    | throwError "rewritten function position is not a function"
  let domainRelType ← mkRelationType domain
  let domainRel ← mkFreshExprMVar domainRelType
  let outputRel ← mkFreshExprMVar (← mkRelationType (← inferType (mkApp child.newExpr arg)))
  let expected ← mkAppM ``respectful #[domainRel, outputRel]
  unless ← isDefEqForValidation child.relation expected do
    throwError "rewritten function relation is not respectful"
  let domainRel ← instantiateMVars domainRel
  let u ← getLevel domain
  let reflType := mkApp2 (mkConst ``Reflexive [u]) domain domainRel
  let reflInst ← synthInstance reflType
  let reflProof := mkAppN (mkConst ``Reflexive.refl [u]) #[domain, domainRel, reflInst, arg]
  let proof := mkApp3 child.proof arg arg reflProof
  return {
    newExpr := mkApp child.newExpr arg
    relation := ← instantiateMVars outputRel
    proof := ← instantiateMVars proof
    orientation := child.orientation
    sideGoals := child.sideGoals
  }

mutual

private partial def rewriteOccurrence (expr rule : Expr) (symm : Bool)
    (inst : InstantiatedRule) (remaining : Nat) : MetaM (Option Result × Nat) := do
  if inst.markReplacement then
    if let some body := annotation? rewriteMark expr then
      let (result?, remaining) ← rewriteChildren body rule symm inst remaining
      let result? := result?.map fun result =>
        { result with newExpr := mkAnnotation rewriteMark result.newExpr }
      return (result?, remaining)
  let saved ← saveState
  if ← isDefEqForRewrite expr inst.lhs then
    if remaining = 1 then
      return (some {
        newExpr := if inst.markReplacement then
          mkAnnotation rewriteMark inst.rhs
        else
          inst.rhs
        relation := inst.relation
        proof := inst.proof
        orientation := inst.orientation
        sideGoals := inst.sideGoals
      }, 0)
    restoreState saved
    let remaining := remaining - 1
    return ← rewriteChildren expr rule symm inst remaining
  restoreState saved
  let childState ← saveState
  try
    let (result, newRemaining) ←
      rewriteChildren expr rule symm inst remaining
    if result.isSome || newRemaining != remaining then
      return (result, newRemaining)
    if isBinderTraversalWrapper expr then
      return (none, remaining)
    let reduced ← withTransparency .instances <| whnf expr
    -- Explicit binders are handled above. Do not inspect implementation lambdas
    -- exposed only by delta reduction of an unrelated named definition.
    if reduced == expr || reduced.isLambda || reduced.isForall then
      return (none, remaining)
    rewriteChildren reduced rule symm inst remaining
  catch ex =>
    restoreState childState
    if isBinderTraversalWrapper expr then
      throw ex
    let reduced ← withTransparency .instances <| whnf expr
    if reduced == expr || reduced.isLambda || reduced.isForall then
      throw ex
    rewriteChildren reduced rule symm inst remaining

private partial def rewriteChildren (expr rule : Expr) (symm : Bool)
    (inst : InstantiatedRule) (remaining : Nat) : MetaM (Option Result × Nat) := do
  match expr with
  | .app f arg =>
      let (fnResult, remaining) ←
        rewriteOccurrence f rule symm inst remaining
      if let some child := fnResult then
        return (some (← liftFunction child arg), remaining)
      let (argResult, remaining) ←
        rewriteOccurrence arg rule symm inst remaining
      if let some child := argResult then
        return (some (← liftArgument f arg child.newExpr child), remaining)
      return (none, remaining)
  | .lam name domain body binderInfo =>
      withLocalDecl name binderInfo domain fun x => do
        let oldBody := body.instantiate1 x
        -- Rule metavariables created outside this scope cannot depend on `x`.
        let localInst ← instantiateOrientedRule rule symm inst.markReplacement
        let (bodyResult, remaining) ←
          rewriteOccurrence oldBody rule symm localInst remaining
        let some child := bodyResult | return (none, remaining)
        let newExpr ← mkLambdaFVars #[x] child.newExpr
        let relationFamily ← mkLambdaFVars #[x] child.relation
        let pointwiseRelation ← mkAppM ``dependentPointwise #[relationFamily]
        let proof ← mkLambdaFVars #[x] child.proof
        return (some {
          newExpr
          relation := pointwiseRelation
          proof
          orientation := child.orientation
          sideGoals := child.sideGoals
        }, remaining)
  | .forallE name domain body binderInfo =>
      unless ← isProp expr do
        return (none, remaining)
      if (← isProp domain) && !body.hasLooseBVar 0 then
        let conceptual ← mkAppM ``implication #[domain, body]
        rewriteChildren conceptual rule symm inst remaining
      else
        let predicate := Expr.lam name domain body binderInfo
        let conceptual ← mkAppM ``forallBinder #[predicate]
        rewriteChildren conceptual rule symm inst remaining
  | _ => return (none, remaining)

end

private def rewriteAtRoot (target : Expr) (rule : Expr) (symm : Bool)
    (occurrence : Nat) (markReplacement : Bool := false) : MetaM Result := do
  let inst ← instantiateOrientedRule rule symm markReplacement
  let (some result, _) ←
      rewriteOccurrence target rule symm inst occurrence
    | throwError "did not find a setoid-rewrite occurrence"
  return result

private partial def eraseRewriteMarks : Expr → Expr
  | .app fn arg => .app (eraseRewriteMarks fn) (eraseRewriteMarks arg)
  | .lam name domain body binderInfo =>
      .lam name (eraseRewriteMarks domain) (eraseRewriteMarks body) binderInfo
  | .forallE name domain body binderInfo =>
      .forallE name (eraseRewriteMarks domain) (eraseRewriteMarks body) binderInfo
  | .letE name type value body nondep =>
      .letE name (eraseRewriteMarks type) (eraseRewriteMarks value)
        (eraseRewriteMarks body) nondep
  | .mdata data body =>
      if data.size == 1 && data.getBool rewriteMark false then
        eraseRewriteMarks body
      else
        .mdata data (eraseRewriteMarks body)
  | .proj typeName index body => .proj typeName index (eraseRewriteMarks body)
  | expression => expression

private def forwardTransport (relation proof input : Expr) : MetaM Expr := do
  let relationType := mkApp (mkConst ``ForwardTransport) relation
  discard <| synthInstance relationType
  mkAppM ``forward_transport #[proof, input]

private def backwardTransport (relation proof input : Expr) : MetaM Expr := do
  let relationType := mkApp (mkConst ``BackwardTransport) relation
  discard <| synthInstance relationType
  mkAppM ``backward_transport #[proof, input]

private def pendingSideGoals (sideGoals : Array MVarId) : MetaM (Array MVarId) := do
  let mut pending := #[]
  for sideGoal in sideGoals do
    unless ← sideGoal.isAssigned do
      pending := pending.push sideGoal
  return pending

private def rewriteTarget (rule : Expr) (symm : Bool) (occurrence : Nat) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let result ← rewriteAtRoot target rule symm occurrence
  unless ← isProp result.newExpr do
    throwError "setoid rewrite did not produce a proposition"
  let newGoal ← mkFreshExprSyntheticOpaqueMVar result.newExpr (← goal.getTag)
  let transformed ← match result.orientation with
    | .forward => backwardTransport result.relation result.proof newGoal
    | .backward => forwardTransport result.relation result.proof newGoal
  unless ← isDefEqForValidation (← inferType transformed) target do
    throwError "internal setoid rewrite target mismatch"
  goal.assign transformed
  replaceMainGoal <| newGoal.mvarId! :: (← pendingSideGoals result.sideGoals).toList

def rewriteTargetOnce (rule : Expr) (symm : Bool := false)
    (occurrence : Nat := 1) : TacticM Unit :=
  rewriteTarget rule symm occurrence

private def rewriteTargetAll (rule : Expr) (symm : Bool) : TacticM Unit := do
  let initialState ← saveState
  let goal ← getMainGoal
  let originalTarget ← goal.getType
  let rec loop (currentGoal : MVarId) (sideGoals : Array MVarId)
      (changed : Bool) : Nat → TacticM (MVarId × Array MVarId)
    | 0 => throwError "setoid rewrite exceeded its occurrence limit"
    | fuel + 1 => do
      let saved ← saveState
      let result? ← currentGoal.withContext do
        let currentTarget ← currentGoal.getType
        try
          return some (← rewriteAtRoot currentTarget rule symm 1 true)
        catch _ =>
          restoreState saved
          return none
      let some result := result? | do
        unless changed do
          throwError "did not find a setoid-rewrite occurrence"
        return (currentGoal, sideGoals)
      let currentTarget ← currentGoal.getType
      let (newGoal, newSideGoals) ← currentGoal.withContext do
        unless ← isProp result.newExpr do
          throwError "setoid rewrite did not produce a proposition"
        let newGoal ← mkFreshExprSyntheticOpaqueMVar result.newExpr
          (← currentGoal.getTag)
        let transformed ← match result.orientation with
          | .forward => backwardTransport result.relation result.proof newGoal
          | .backward => forwardTransport result.relation result.proof newGoal
        unless ← isDefEqForValidation (← inferType transformed) currentTarget do
          throwError "internal setoid rewrite target mismatch"
        currentGoal.assign transformed
        return (newGoal.mvarId!, ← pendingSideGoals result.sideGoals)
      let sideGoals := newSideGoals ++ sideGoals
      loop newGoal sideGoals true fuel
  let (newGoal, sideGoals) ← loop goal #[] false 4096
  let cleanTarget := eraseRewriteMarks (← newGoal.getType)
  let comparisonState ← saveState
  let unchanged ← newGoal.withContext do
    isDefEqForValidation cleanTarget originalTarget
  restoreState comparisonState
  if unchanged then
    restoreState initialState
    throwError "setoid rewrite failed to progress"
  let cleanGoal ← newGoal.withContext do
    newGoal.change cleanTarget false
  replaceMainGoal (cleanGoal :: sideGoals.toList)

private def rewriteLocal (rule : Expr) (symm : Bool) (occurrence : Nat)
    (fvarId : FVarId) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  let oldType ← fvarId.getType
  let result ← rewriteAtRoot oldType rule symm occurrence
  unless ← isProp result.newExpr do
    throwError "setoid rewrite did not produce a proposition"
  let newProof ← match result.orientation with
    | .forward => forwardTransport result.relation result.proof (mkFVar fvarId)
    | .backward => backwardTransport result.relation result.proof (mkFVar fvarId)
  unless ← isDefEqForValidation (← inferType newProof) result.newExpr do
    throwError "internal setoid rewrite hypothesis mismatch"
  let replaced ← goal.replace fvarId newProof (some result.newExpr)
  replaceMainGoal <| replaced.mvarId :: (← pendingSideGoals result.sideGoals).toList

private def evalRelRw (rules locSyntax : Syntax) (occurrence : Nat) : TacticM Unit := do
  unless occurrence > 0 do
    throwError "setoid rewrite occurrence must be positive"
  let location := expandOptLocation locSyntax
  withRWRulesSeq rules[0] rules fun symm term => do
    let proof ← withMainContext <| Lean.Elab.Tactic.elabTermForApply term
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    withLocation location
      (rewriteLocal proof symm occurrence)
      (rewriteTarget proof symm occurrence)
      (throwTacticEx `rel_rw · "did not find a setoid-rewrite occurrence")

elab "rel_rw" rules:rwRuleSeq loc:(location)? : tactic => do
  let locSyntax := mkNullNode <| loc.map (fun stx => stx.raw) |>.toArray
  evalRelRw rules.raw locSyntax 1

elab "rel_rw" "(" "occs" ":=" occurrence:num ")" rules:rwRuleSeq
    loc:(location)? : tactic => do
  let locSyntax := mkNullNode <| loc.map (fun stx => stx.raw) |>.toArray
  evalRelRw rules.raw locSyntax occurrence.getNat

private def evalRelRwAll (rules : Syntax) : TacticM Unit := do
  withRWRulesSeq rules[0] rules fun symm term => do
    let proof ← withMainContext <| Lean.Elab.Tactic.elabTermForApply term
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    rewriteTargetAll proof symm

elab "rel_rw!" rules:rwRuleSeq : tactic =>
  evalRelRwAll rules.raw

end SetoidRewrite

end AUXLib
