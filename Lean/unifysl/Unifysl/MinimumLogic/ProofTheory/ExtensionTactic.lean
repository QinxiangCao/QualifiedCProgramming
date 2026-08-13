import Lean
import Unifysl.Lib.register_typeclass
import Unifysl.MinimumLogic.ProofTheory.TheoryOfJudgement

/-!
Coq inventory from `MinimumLogic/ProofTheory/ExtensionTactic.v`:
- Empty register kinds:
  `P2D_reg`, `D2P_reg`, `P2D1_reg`, `P2E_reg`, `D12P_reg`, `D12E_reg`.
- Ltac tactics:
  `pose_proof_P2D_instance`, `pose_proof_D2P_instance`,
  `pose_proof_P2D1_instance`, `pose_proof_P2E_instance`,
  `pose_proof_D12P_instance`, `AddSequentCalculus`,
  `AddAxiomatizationFromSequentCalculus`,
  `AddAxiomatizationFromDeduction`, `AddAxiomatization`, `AddDeduction`,
  `AddEquiv`.
- Register instances:
  `reg_Axiomatization2SequentCalculus_GammaPD`,
  `reg_Axiomatization2SequentCalculus_bSC`,
  `reg_Axiomatization2SequentCalculus_fwSC`,
  `reg_Axiomatization2SequentCalculus_minSC`,
  `reg_SequentCalculus2Axiomatization_GammaDP`,
  `reg_SequentCalculus2Axiomatization_minAX`,
  `reg_Axiomatization2Deduction_bD`,
  `reg_Axiomatization2Equiv_bE`.
- Coq smoke-test sections are represented below by Lean `example`s.
-/

open Lean Meta Elab Term Tactic

universe u

namespace Unifysl

inductive P2D_reg : Type where
inductive D2P_reg : Type where
inductive P2D1_reg : Type where
inductive P2E_reg : Type where
inductive D12P_reg : Type where
inductive D12E_reg : Type where

structure ProofRegistration where
  localName : Name
  proofName : Name

namespace ExtensionTactic

private partial def nameExpr? : Expr -> Option Name
  | Expr.const ``Lean.Name.anonymous _ => some Name.anonymous
  | Expr.app (Expr.const ``Lean.Name.mkStr1 _) (Expr.lit (.strVal s₁)) =>
      some <| Name.mkSimple s₁
  | Expr.app (Expr.app (Expr.const ``Lean.Name.mkStr2 _) (Expr.lit (.strVal s₁)))
      (Expr.lit (.strVal s₂)) =>
      some <| .str (Name.mkSimple s₁) s₂
  | Expr.app
      (Expr.app (Expr.app (Expr.const ``Lean.Name.mkStr3 _) (Expr.lit (.strVal s₁)))
        (Expr.lit (.strVal s₂))) (Expr.lit (.strVal s₃)) =>
      some <| .str (.str (Name.mkSimple s₁) s₂) s₃
  | Expr.app
      (Expr.app
        (Expr.app (Expr.app (Expr.const ``Lean.Name.mkStr4 _) (Expr.lit (.strVal s₁)))
          (Expr.lit (.strVal s₂))) (Expr.lit (.strVal s₃))) (Expr.lit (.strVal s₄)) =>
      some <| .str (.str (.str (Name.mkSimple s₁) s₂) s₃) s₄
  | Expr.app (Expr.app (Expr.const ``Lean.Name.str _) pre) (Expr.lit (.strVal s)) =>
      nameExpr? pre |>.map fun n => .str n s
  | Expr.app (Expr.app (Expr.const ``Lean.Name.num _) pre) (Expr.lit (.natVal n)) =>
      nameExpr? pre |>.map fun name => .num name n
  | _ => none

private def proofRegistrationExpr? (e : Expr) : Option ProofRegistration :=
  e.withApp fun fn args =>
    if fn.isConstOf ``ProofRegistration.mk && args.size == 2 then
      match nameExpr? args[0]!, nameExpr? args[1]! with
      | some localName, some proofName => some { localName, proofName }
      | _, _ => none
    else
      none

private def getNthRegistration (kind : Name) (n : Nat) : TacticM ProofRegistration :=
  withMainContext do
    let stx ← `(get_nth $(mkIdent kind) $(Syntax.mkNumLit (toString n)))
    let e ← Term.elabTerm stx (mkConst ``ProofRegistration)
    let e ← instantiateMVars e
    let e ← whnf e
    match proofRegistrationExpr? e with
    | some reg => pure reg
    | none => throwError "registered entry {n} for {kind} is not a ProofRegistration"

private def languageType? (type : Expr) : MetaM Bool := do
  let type ← whnf type
  pure <| type.isConstOf ``Language

private def findLanguage : TacticM Expr := withMainContext do
  let lctx ← getLCtx
  let langs ← lctx.foldlM (init := #[]) fun acc decl => do
    if decl.isImplementationDetail then
      pure acc
    else if ← languageType? decl.type then
      pure <| acc.push (mkFVar decl.fvarId)
    else
      pure acc
  match langs.size with
  | 0 => throwError "ExtensionTactic could not find a `Language` local variable"
  | 1 => pure langs[0]!
  | _ => throwError "ExtensionTactic found more than one `Language`; please disambiguate the context"

private def assertLocalInstance (baseName : Name) (type value : Expr) : TacticM FVarId :=
  withMainContext do
    let userName ← mkFreshUserName baseName
    let type ← instantiateMVars type
    let value ← instantiateMVars value
    if type.hasExprMVar || value.hasExprMVar then
      throwError "local instance {userName} contains unresolved metavariables"
    let goal ← getMainGoal
    let (ids, goal) ← goal.assertHypotheses #[
      { userName := userName
        type := type
        value := value
        binderInfo := BinderInfo.instImplicit
        kind := LocalDeclKind.default }]
    replaceMainGoal [goal]
    withMainContext do
      discard <| synthInstance type
    pure ids[0]!

private partial def applyContextArguments (proof : Expr) : TacticM Expr :=
  withMainContext do
    let proof ← instantiateMVars proof
    let type ← inferType proof
    let type ← instantiateMVars type
    let type ← whnf type
    match type with
    | Expr.forallE _ argType _ _ =>
        let argType ← instantiateMVars argType
        let argType ← whnf argType
        let arg ←
          if ← languageType? argType then
            findLanguage
          else
            synthInstance argType
        applyContextArguments (mkApp proof arg)
    | _ =>
        pure proof

private def languageLevel (L : Expr) : MetaM Level := do
  let type ← whnf (← inferType L)
  match type.getAppFn with
  | Expr.const ``Language [u] => pure u
  | _ => throwError "expected a Language expression, got{indentExpr type}"

private def mkLanguageConstApp (declName : Name) (L : Expr) (args : Array Expr) :
    MetaM Expr := do
  let u ← languageLevel L
  pure <| mkAppN (mkConst declName [u]) args

private def poseRegistration (reg : ProofRegistration) : TacticM Unit := do
  let proof ← withMainContext do
    let proof ← mkConstWithFreshMVarLevels reg.proofName
    let proof ← applyContextArguments proof
    RegisterTypeclass.applyInstanceArguments proof
  let type ← withMainContext do
    let proof ← instantiateMVars proof
    let type ← inferType proof
    let type ← instantiateMVars type
    if proof.hasExprMVar || type.hasExprMVar then
      throwError "registered proof {reg.proofName} produced unresolved metavariables"
    pure type
  discard <| assertLocalInstance reg.localName type proof

private def poseRegisteredProof (kind : Name) (n : Nat) : TacticM Unit := do
  let reg ← getNthRegistration kind n
  let saved ← saveState
  try
    poseRegistration reg
  catch _ =>
    restoreState saved

private def evalPoseRegisteredProof (kind : Name) (nStx : Syntax) : TacticM Unit :=
  withMainContext do
    let nExpr ← Term.elabTerm nStx (mkConst ``Nat)
    let some n ← (evalNat nExpr).run
      | throwError "registered proof index must reduce to a natural number"
    poseRegisteredProof kind n

private def addSequentCalculusCore : TacticM Unit := do
  let L ← findLanguage
  let minL ← withMainContext <| synthInstance (← mkAppM ``MinimumLanguage #[L])
  let gammaP ← withMainContext <| synthInstance (← mkAppM ``Provable #[L])
  let gammaDId ← do
    let type ← withMainContext <| mkAppM ``Derivable #[L]
    let value ← withMainContext <| mkLanguageConstApp ``Provable2Derivable L #[L, minL, gammaP]
    assertLocalInstance `GammaD type value
  let gammaD := mkFVar gammaDId
  let (type, value) ← withMainContext do
    let type ← mkAppM ``DerivableProvable #[L, gammaP, gammaD]
    let value ← mkLanguageConstApp ``Provable2Derivable_Normal L #[L, minL, gammaP]
    pure (type, value)
  discard <| assertLocalInstance `GammaDP type value
  RegisterTypeclass.rec_from_n 0 (poseRegisteredProof ``P2D_reg)

private def addAxiomatizationFromSequentCalculusCore : TacticM Unit := do
  let L ← findLanguage
  let gammaD ← withMainContext <| synthInstance (← mkAppM ``Derivable #[L])
  let gammaPId ← do
    let type ← withMainContext <| mkAppM ``Provable #[L]
    let value ← withMainContext <| mkLanguageConstApp ``Derivable2Provable L #[L, gammaD]
    assertLocalInstance `GammaP type value
  let gammaP := mkFVar gammaPId
  let (type, value) ← withMainContext do
    let type ← mkAppM ``ProvableDerivable #[L, gammaP, gammaD]
    let value ← mkLanguageConstApp ``Derivable2Provable_Normal L #[L, gammaD]
    pure (type, value)
  discard <| assertLocalInstance `GammaPD type value
  RegisterTypeclass.rec_from_n 0 (poseRegisteredProof ``D2P_reg)

private def addAxiomatizationFromDeductionCore : TacticM Unit := do
  let L ← findLanguage
  let minL ← withMainContext <| synthInstance (← mkAppM ``MinimumLanguage #[L])
  let gammaD1 ← withMainContext <| synthInstance (← mkAppM ``Derivable1 #[L])
  let gammaPId ← do
    let type ← withMainContext <| mkAppM ``Provable #[L]
    let value ← withMainContext <| mkLanguageConstApp ``Derivable12Provable L #[L, minL, gammaD1]
    assertLocalInstance `GammaP type value
  let gammaP := mkFVar gammaPId
  let (type, value) ← withMainContext do
    let type ← mkAppM ``ProvableDerivable1 #[L, gammaP, gammaD1]
    let value ← mkLanguageConstApp ``Derivable12Provable_Normal L #[L, minL, gammaD1]
    pure (type, value)
  discard <| assertLocalInstance `GammaPD1 type value
  RegisterTypeclass.rec_from_n 0 (poseRegisteredProof ``D12P_reg)

private def addAxiomatizationCore : TacticM Unit := do
  let L ← findLanguage
  let hasDerivable ← withMainContext do
    try
      discard <| synthInstance (← mkAppM ``Derivable #[L])
      pure true
    catch _ =>
      pure false
  if hasDerivable then
    addAxiomatizationFromSequentCalculusCore
  else
    let hasDerivable1 ← withMainContext do
      try
        discard <| synthInstance (← mkAppM ``Derivable1 #[L])
        pure true
      catch _ =>
        pure false
    if hasDerivable1 then
      addAxiomatizationFromDeductionCore
    else
      throwError "AddAxiomatization needs a `Derivable` or `Derivable1` instance"

private def addDeductionCore : TacticM Unit := do
  let L ← findLanguage
  let minL ← withMainContext <| synthInstance (← mkAppM ``MinimumLanguage #[L])
  let gammaP ← withMainContext <| synthInstance (← mkAppM ``Provable #[L])
  let gammaD1Id ← do
    let type ← withMainContext <| mkAppM ``Derivable1 #[L]
    let value ← withMainContext <| mkLanguageConstApp ``Provable2Derivable1 L #[L, minL, gammaP]
    assertLocalInstance `GammaD1 type value
  let gammaD1 := mkFVar gammaD1Id
  let (type, value) ← withMainContext do
    let type ← mkAppM ``Derivable1Provable #[L, gammaP, gammaD1]
    let value ← mkLanguageConstApp ``Provable2Derivable1_Normal L #[L, minL, gammaP]
    pure (type, value)
  discard <| assertLocalInstance `GammaD1P type value
  RegisterTypeclass.rec_from_n 0 (poseRegisteredProof ``P2D1_reg)

private def addEquivCore : TacticM Unit := do
  let L ← findLanguage
  let minL ← withMainContext <| synthInstance (← mkAppM ``MinimumLanguage #[L])
  let gammaP ← withMainContext <| synthInstance (← mkAppM ``Provable #[L])
  let gammaEId ← do
    let type ← withMainContext <| mkAppM ``LogicEquiv #[L]
    let value ← withMainContext <| mkLanguageConstApp ``Provable2Equiv L #[L, minL, gammaP]
    assertLocalInstance `GammaE type value
  let gammaE := mkFVar gammaEId
  let (type, value) ← withMainContext do
    let type ← mkAppM ``EquivProvable #[L, gammaP, gammaE]
    let value ← mkLanguageConstApp ``Provable2Equiv_Normal L #[L, minL, gammaP]
    pure (type, value)
  discard <| assertLocalInstance `GammaEP type value
  RegisterTypeclass.rec_from_n 0 (poseRegisteredProof ``P2E_reg)

private def checkP2DInstances : TacticM Unit := withMainContext do
  let L ← findLanguage
  let gammaP ← synthInstance (← mkAppM ``Provable #[L])
  let gammaD ← synthInstance (← mkAppM ``Derivable #[L])
  discard <| synthInstance (← mkAppM ``ProvableDerivable #[L, gammaP, gammaD])
  discard <| synthInstance (← mkAppM ``BasicSequentCalculus #[L, gammaD])
  discard <| synthInstance (← mkAppM ``FiniteWitnessedSequentCalculus #[L, gammaD])
  discard <| synthInstance (← mkAppM ``MinimumSequentCalculus #[L, gammaD])

private def checkD2PInstances : TacticM Unit := withMainContext do
  let L ← findLanguage
  let gammaP ← synthInstance (← mkAppM ``Provable #[L])
  let gammaD ← synthInstance (← mkAppM ``Derivable #[L])
  discard <| synthInstance (← mkAppM ``ProvableDerivable #[L, gammaP, gammaD])
  discard <| synthInstance (← mkAppM ``DerivableProvable #[L, gammaP, gammaD])
  discard <| synthInstance (← mkAppM ``MinimumAxiomatization #[L, gammaP])

private def checkD12PInstances : TacticM Unit := withMainContext do
  let L ← findLanguage
  let gammaP ← synthInstance (← mkAppM ``Provable #[L])
  let gammaD1 ← synthInstance (← mkAppM ``Derivable1 #[L])
  discard <| synthInstance (← mkAppM ``ProvableDerivable1 #[L, gammaP, gammaD1])

private def checkP2D1Instances : TacticM Unit := withMainContext do
  let L ← findLanguage
  let gammaP ← synthInstance (← mkAppM ``Provable #[L])
  let gammaD1 ← synthInstance (← mkAppM ``Derivable1 #[L])
  discard <| synthInstance (← mkAppM ``Derivable1Provable #[L, gammaP, gammaD1])
  discard <| synthInstance (← mkAppM ``BasicDeduction #[L, gammaD1])

private def checkP2EInstances : TacticM Unit := withMainContext do
  let L ← findLanguage
  let gammaP ← synthInstance (← mkAppM ``Provable #[L])
  let gammaE ← synthInstance (← mkAppM ``LogicEquiv #[L])
  discard <| synthInstance (← mkAppM ``EquivProvable #[L, gammaP, gammaE])
  discard <| synthInstance (← mkAppM ``BasicLogicEquiv #[L, gammaE])

end ExtensionTactic

syntax "pose_proof_P2D_instance " term : tactic
syntax "pose_proof_D2P_instance " term : tactic
syntax "pose_proof_P2D1_instance " term : tactic
syntax "pose_proof_P2E_instance " term : tactic
syntax "pose_proof_D12P_instance " term : tactic
syntax "AddSequentCalculus" : tactic
syntax "AddAxiomatizationFromSequentCalculus" : tactic
syntax "AddAxiomatizationFromDeduction" : tactic
syntax "AddAxiomatization" : tactic
syntax "AddDeduction" : tactic
syntax "AddEquiv" : tactic

def AddSequentCalculus : Unit := ()
def AddAxiomatizationFromSequentCalculus : Unit := ()
def AddAxiomatizationFromDeduction : Unit := ()
def AddAxiomatization : Unit := ()
def AddDeduction : Unit := ()
def AddEquiv : Unit := ()

elab "pose_proof_P2D_instance " n:term : tactic =>
  ExtensionTactic.evalPoseRegisteredProof ``P2D_reg n

elab "pose_proof_D2P_instance " n:term : tactic =>
  ExtensionTactic.evalPoseRegisteredProof ``D2P_reg n

elab "pose_proof_P2D1_instance " n:term : tactic =>
  ExtensionTactic.evalPoseRegisteredProof ``P2D1_reg n

elab "pose_proof_P2E_instance " n:term : tactic =>
  ExtensionTactic.evalPoseRegisteredProof ``P2E_reg n

elab "pose_proof_D12P_instance " n:term : tactic =>
  ExtensionTactic.evalPoseRegisteredProof ``D12P_reg n

elab "AddSequentCalculus" : tactic =>
  ExtensionTactic.addSequentCalculusCore

elab "AddAxiomatizationFromSequentCalculus" : tactic =>
  ExtensionTactic.addAxiomatizationFromSequentCalculusCore

elab "AddAxiomatizationFromDeduction" : tactic =>
  ExtensionTactic.addAxiomatizationFromDeductionCore

elab "AddAxiomatization" : tactic =>
  ExtensionTactic.addAxiomatizationCore

elab "AddDeduction" : tactic =>
  ExtensionTactic.addDeductionCore

elab "AddEquiv" : tactic =>
  ExtensionTactic.addEquivCore

instance reg_Axiomatization2SequentCalculus_GammaPD :
    RegisterClass P2D_reg
      (ProofRegistration.mk `GammaPD ``Axiomatization2SequentCalculus_GammaPD) 0 := {}

instance reg_Axiomatization2SequentCalculus_bSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `bSC ``Axiomatization2SequentCalculus_bSC) 1 := {}

instance reg_Axiomatization2SequentCalculus_fwSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `fwSC ``Axiomatization2SequentCalculus_fwSC) 2 := {}

instance reg_Axiomatization2SequentCalculus_minSC :
    RegisterClass P2D_reg
      (ProofRegistration.mk `minSC ``Axiomatization2SequentCalculus_minSC) 3 := {}

instance reg_SequentCalculus2Axiomatization_GammaDP :
    RegisterClass D2P_reg
      (ProofRegistration.mk `GammaDP ``SequentCalculus2Axiomatization_GammaDP) 0 := {}

instance reg_SequentCalculus2Axiomatization_minAX :
    RegisterClass D2P_reg
      (ProofRegistration.mk `minAX ``SequentCalculus2Axiomatization_minAX) 1 := {}

instance reg_Axiomatization2Deduction_bD :
    RegisterClass P2D1_reg
      (ProofRegistration.mk `bD ``Axiomatization2Deduction_bD) 0 := {}

instance reg_Axiomatization2Equiv_bE :
    RegisterClass P2E_reg
      (ProofRegistration.mk `bE ``Axiomatization2Equiv_bE) 0 := {}

section Examples

example {L : Language.{u}} [MinimumLanguage L] [GammaP : Provable L]
    [MinimumAxiomatization L GammaP] : True := by
  AddSequentCalculus
  run_tac ExtensionTactic.checkP2DInstances
  trivial

example {L : Language.{u}} [MinimumLanguage L] [GammaD : Derivable L]
    [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
    [FiniteWitnessedSequentCalculus L GammaD] : True := by
  AddAxiomatizationFromSequentCalculus
  run_tac ExtensionTactic.checkD2PInstances
  trivial

example {L : Language.{u}} [MinimumLanguage L] [GammaD1 : Derivable1 L]
    [BasicDeduction L GammaD1] : True := by
  AddAxiomatizationFromDeduction
  run_tac ExtensionTactic.checkD12PInstances
  trivial

example {L : Language.{u}} [MinimumLanguage L] [GammaD : Derivable L]
    [BasicSequentCalculus L GammaD] [MinimumSequentCalculus L GammaD]
    [FiniteWitnessedSequentCalculus L GammaD] : True := by
  AddAxiomatization
  run_tac ExtensionTactic.checkD2PInstances
  trivial

example {L : Language.{u}} [MinimumLanguage L] [GammaD1 : Derivable1 L]
    [BasicDeduction L GammaD1] : True := by
  AddAxiomatization
  run_tac ExtensionTactic.checkD12PInstances
  trivial

example {L : Language.{u}} [MinimumLanguage L] [GammaP : Provable L]
    [_GammaD : Derivable L] [MinimumAxiomatization L GammaP] : True := by
  AddDeduction
  run_tac ExtensionTactic.checkP2D1Instances
  trivial

example {L : Language.{u}} [MinimumLanguage L] [GammaP : Provable L]
    [_GammaD : Derivable L] [MinimumAxiomatization L GammaP] : True := by
  AddEquiv
  run_tac ExtensionTactic.checkP2EInstances
  trivial

end Examples

end Unifysl
