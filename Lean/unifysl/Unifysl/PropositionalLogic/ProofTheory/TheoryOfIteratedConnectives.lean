import Lean
import Unifysl.PropositionalLogic.ProofTheory.ProofTheoryPatterns

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
Coq inventory from `PropositionalLogic/ProofTheory/TheoryOfIteratedConnectives.v`:
- Definition classes:
  `IterAndDefinition_left`, `IterAndDefinition_right`,
  `IterOrDefinition_left`, `IterOrDefinition_right`.
- Fold-based language constructors:
  `FoldLeftAnd2IterAnd`, `FoldRightAnd2IterAnd`.
- Normality lemmas:
  `FoldLeftAnd2IterAnd_Normal`, `FoldRightAnd2IterAnd_Normal`.
- Definition-to-axiomatization lemmas:
  `IterAndFromDefToAX_L2L`, `IterAndFromDefToAX_R2L`.
- Ltac:
  `AddConnective_iter_andp`.
-/

universe u

namespace Unifysl

open PropositionalLanguageNotation

private theorem provable_iffp_trans_local {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {x y z : @Language.expr L} :
    (|-- (x ⟷ y)) -> (|-- (y ⟷ z)) -> |-- (x ⟷ z) := by
  intro hxy hyz
  have hxy' : |-- (x ⟶ y) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (x ⟷ y) (x ⟶ y)
      (IffAxiomatization.provable_iffp_elim1 x y) hxy
  have hyz' : |-- (y ⟶ z) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (y ⟷ z) (y ⟶ z)
      (IffAxiomatization.provable_iffp_elim1 y z) hyz
  have hzy' : |-- (z ⟶ y) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (y ⟷ z) (z ⟶ y)
      (IffAxiomatization.provable_iffp_elim2 y z) hyz
  have hyx' : |-- (y ⟶ x) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (x ⟷ y) (y ⟶ x)
      (IffAxiomatization.provable_iffp_elim2 x y) hxy
  have hxz : |-- (x ⟶ z) := solve_impp_trans x y z hxy' hyz'
  have hzx : |-- (z ⟶ x) := solve_impp_trans z y x hzy' hyx'
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ z) ((z ⟶ x) ⟶ (x ⟷ z))
    (IffAxiomatization.provable_iffp_intros x z) hxz
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (z ⟶ x) (x ⟷ z) hstep hzx

private theorem provable_iffp_refl_local {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    (x : @Language.expr L) :
    |-- (x ⟷ x) := by
  have hxx : |-- (x ⟶ x) := provable_impp_refl x
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ x) ((x ⟶ x) ⟶ (x ⟷ x))
    (IffAxiomatization.provable_iffp_intros x x) hxx
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ x) (x ⟷ x) hstep hxx

private theorem provable_iffp_symm_local {L : Language.{u}}
    [MinimumLanguage L] [IffLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [IffAxiomatization L Gamma]
    {x y : @Language.expr L} :
    (|-- (x ⟷ y)) -> |-- (y ⟷ x) := by
  intro hxy
  have hxy' : |-- (x ⟶ y) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (x ⟷ y) (x ⟶ y)
      (IffAxiomatization.provable_iffp_elim1 x y) hxy
  have hyx' : |-- (y ⟶ x) :=
    MinimumAxiomatization.modus_ponens
      (Gamma := Gamma) (x ⟷ y) (y ⟶ x)
      (IffAxiomatization.provable_iffp_elim2 x y) hxy
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (y ⟶ x) ((x ⟶ y) ⟶ (y ⟷ x))
    (IffAxiomatization.provable_iffp_intros y x) hyx'
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ y) (y ⟷ x) hstep hxy'

private theorem provable_impp_andp_local {L : Language.{u}}
    [MinimumLanguage L] [AndLanguage L] [Gamma : Provable L]
    [MinimumAxiomatization L Gamma] [AndAxiomatization L Gamma]
    (x y z : @Language.expr L) :
    (|-- (x ⟶ y)) -> (|-- (x ⟶ z)) -> |-- (x ⟶ (y && z)) := by
  intro hxy hxz
  have hyz : |-- (y ⟶ z ⟶ (y && z)) :=
    AndAxiomatization.provable_andp_intros y z
  have hxzyz : |-- (x ⟶ z ⟶ (y && z)) :=
    aux_minimun_rule02 x y (z ⟶ (y && z)) hxy hyz
  have hstep := MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ z ⟶ (y && z))
    ((x ⟶ z) ⟶ (x ⟶ (y && z)))
    (MinimumAxiomatization.axiom2 x z (y && z)) hxzyz
  exact MinimumAxiomatization.modus_ponens
    (Gamma := Gamma) (x ⟶ z) (x ⟶ (y && z)) hstep hxz

class IterAndDefinition_left (L : Language.{u}) [AndLanguage L]
    [TrueLanguage L] [semiOutParam (IterAndLanguage L)] : Prop where
  iter_andp_def_l :
    forall xs : List (@Language.expr L),
      iter_andp xs = List.foldl andp TT xs

class IterAndDefinition_right (L : Language.{u}) [AndLanguage L]
    [TrueLanguage L] [semiOutParam (IterAndLanguage L)] : Prop where
  iter_andp_def_r :
    forall xs : List (@Language.expr L),
      iter_andp xs = List.foldr andp TT xs

class IterOrDefinition_left (L : Language.{u}) [OrLanguage L]
    [FalseLanguage L] [semiOutParam (IterOrLanguage L)] : Prop where
  iter_orp_def_l :
    forall xs : List (@Language.expr L),
      iter_orp xs = List.foldl orp FF xs

class IterOrDefinition_right (L : Language.{u}) [OrLanguage L]
    [FalseLanguage L] [semiOutParam (IterOrLanguage L)] : Prop where
  iter_orp_def_r :
    forall xs : List (@Language.expr L),
      iter_orp xs = List.foldr orp FF xs

def FoldLeftAnd2IterAnd {L : Language.{u}} [AndLanguage L]
    [TrueLanguage L] : IterAndLanguage L where
  iter_andp := fun xs => List.foldl andp TT xs

instance (priority := 100) FoldLeftAnd2IterAnd_instance {L : Language.{u}}
    [AndLanguage L] [TrueLanguage L] : IterAndLanguage L :=
  FoldLeftAnd2IterAnd (L := L)

def FoldRightAnd2IterAnd {L : Language.{u}} [AndLanguage L]
    [TrueLanguage L] : IterAndLanguage L where
  iter_andp := fun xs => List.foldr andp TT xs

theorem FoldLeftAnd2IterAnd_Normal {L : Language.{u}} [AndLanguage L]
    [TrueLanguage L] :
    @IterAndDefinition_left L _ _
      (FoldLeftAnd2IterAnd (L := L) : IterAndLanguage L) := by
  exact @IterAndDefinition_left.mk L
    (inferInstance : AndLanguage L) (inferInstance : TrueLanguage L)
    (FoldLeftAnd2IterAnd (L := L)) (by intro xs; rfl)

instance (priority := 100) FoldLeftAnd2IterAnd_Normal_instance
    {L : Language.{u}} [AndLanguage L] [TrueLanguage L] :
    IterAndDefinition_left L :=
  FoldLeftAnd2IterAnd_Normal (L := L)

theorem FoldRightAnd2IterAnd_Normal {L : Language.{u}} [AndLanguage L]
    [TrueLanguage L] :
    @IterAndDefinition_right L _ _
      (FoldRightAnd2IterAnd (L := L) : IterAndLanguage L) := by
  exact @IterAndDefinition_right.mk L
    (inferInstance : AndLanguage L) (inferInstance : TrueLanguage L)
    (FoldRightAnd2IterAnd (L := L)) (by intro xs; rfl)

theorem IterAndFromDefToAX_L2L {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [TrueLanguage L] [IterAndLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [AndAxiomatization L GammaP] [IffAxiomatization L GammaP]
    [TrueAxiomatization L GammaP] [IterAndDefinition_left L] :
    IterAndAxiomatization_left L GammaP := by
  constructor
  intro xs
  rw [IterAndDefinition_left.iter_andp_def_l xs]
  exact provable_iffp_refl_local (List.foldl andp TT xs)

instance (priority := 100) IterAndFromDefToAX_L2L_instance
    {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [TrueLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [AndAxiomatization L GammaP] [IffAxiomatization L GammaP]
    [TrueAxiomatization L GammaP] :
    IterAndAxiomatization_left L GammaP :=
  IterAndFromDefToAX_L2L (L := L) (GammaP := GammaP)

theorem IterAndFromDefToAX_R2L {L : Language.{u}} [MinimumLanguage L]
    [AndLanguage L] [IffLanguage L] [TrueLanguage L] [IterAndLanguage L]
    [GammaP : Provable L] [MinimumAxiomatization L GammaP]
    [AndAxiomatization L GammaP] [IffAxiomatization L GammaP]
    [TrueAxiomatization L GammaP] [IterAndDefinition_right L] :
    IterAndAxiomatization_left L GammaP := by
  constructor
  intro xs
  rw [IterAndDefinition_right.iter_andp_def_r xs]
  letI : ProofTheoryPatternsP.Monotonicity L GammaP andp := by
    constructor
    intro x1 y1 x2 y2 hx hy
    exact provable_impp_andp_local (x1 && y1) x2 y2
      (solve_impp_trans (x1 && y1) x1 x2
        (AndAxiomatization.provable_andp_elim1 x1 y1) hx)
      (solve_impp_trans (x1 && y1) y1 y2
        (AndAxiomatization.provable_andp_elim2 x1 y1) hy)
  letI : ProofTheoryPatternsP.Associativity L GammaP andp := by
    constructor
    · intro x y z
      exact provable_andp_impp_assoc2 x y z
    · intro x y z
      exact provable_andp_impp_assoc1 x y z
  letI : ProofTheoryPatternsP.LeftUnit L GammaP TT andp := by
    constructor
    · exact provable_truep_andp_derives
    · exact provable_derives_truep_andp
  letI : ProofTheoryPatternsP.RightUnit L GammaP TT andp := by
    constructor
    · exact provable_andp_truep_derives
    · exact provable_derives_andp_truep
  have hfold : |-- (List.foldl andp TT xs ⟷ List.foldr andp TT xs) :=
    PropositionalLogic.ProofTheoryPatterns.P.assoc_fold_left_fold_right_equiv
      (prodp := andp) (e := TT) xs
  exact provable_iffp_symm_local hfold

open Lean Meta Elab Tactic

syntax "AddConnective_iter_andp" : tactic

private def localLanguage? (type : Expr) : MetaM Bool := do
  pure <| (← whnf type).isConstOf ``Language

private def findLocalLanguage : TacticM (Name × Expr) := withMainContext do
  let lctx ← getLCtx
  let mut found : Array (Name × Expr) := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if ← localLanguage? decl.type then
        found := found.push (decl.userName, mkFVar decl.fvarId)
  match found.size with
  | 1 => pure found[0]!
  | 0 => throwError "AddConnective_iter_andp could not find a local `Language`"
  | _ => throwError "AddConnective_iter_andp found more than one local `Language`"

private def findLocalProvableName (L : Expr) : TacticM Name := withMainContext do
  let lctx ← getLCtx
  let mut found : Array Name := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      let type ← whnf decl.type
      if type.isAppOf ``Provable then
        let args := type.getAppArgs
        if args.size == 1 then
          if ← isDefEq args[0]! L then
            found := found.push decl.userName
  match found.size with
  | 1 => pure found[0]!
  | 0 => throwError "AddConnective_iter_andp could not find a local `Provable` for the current language"
  | _ => throwError "AddConnective_iter_andp found more than one local `Provable` for the current language"

private def addConnectiveIterAndp : TacticM Unit := withMainContext do
  let (LName, LExpr) ← findLocalLanguage
  let GammaPName ← findLocalProvableName LExpr
  let LId := mkIdent LName
  let GammaPId := mkIdent GammaPName
  discard <| synthInstance (← Term.elabType (← `(IterAndLanguage $LId)))
  discard <| synthInstance (← Term.elabType (← `(IterAndDefinition_left $LId)))
  discard <| synthInstance (← Term.elabType
    (← `(IterAndAxiomatization_left $LId $GammaPId)))

elab "AddConnective_iter_andp" : tactic => addConnectiveIterAndp

end Unifysl
