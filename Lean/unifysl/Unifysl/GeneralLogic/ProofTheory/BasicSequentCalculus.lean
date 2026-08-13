import Unifysl.GeneralLogic.ProofTheory.TheoryOfSequentCalculus

/-!
Coq inventory from `GeneralLogic/ProofTheory/BasicSequentCalculus.v`:
- Class `BasicSequentCalculus` with fields `deduction_weaken`,
  `derivable_assum`, `deduction_subst`.
- Class `FiniteWitnessedSequentCalculus` with field
  `derivable_finite_witnessed`.
- Lemmas: `deduction_subst1`, `derivable_trans`, `deduction_weaken1`,
  `derivable_assum1`, `contextual_derivable_finite_witnessed`,
  `WeakSubst12BasicSequentCalculus`.
- Tactic: `solve_assum`.
-/

universe u

namespace Unifysl

class BasicSequentCalculus (L : Language.{u}) (Gamma : Derivable L) : Prop where
  deduction_weaken :
    forall (Phi Psi : context (L := L)) (x : @Language.expr L),
      Included _ Phi Psi -> Gamma.derivable Phi x -> Gamma.derivable Psi x
  derivable_assum :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      In _ Phi x -> Gamma.derivable Phi x
  deduction_subst :
    forall (Phi Psi : context (L := L)) (y : @Language.expr L),
      (forall x, Psi x -> Gamma.derivable Phi x) ->
        Gamma.derivable (Union _ Phi Psi) y -> Gamma.derivable Phi y

class FiniteWitnessedSequentCalculus (L : Language.{u}) (Gamma : Derivable L) :
    Prop where
  derivable_finite_witnessed :
    forall (Phi : context (L := L)) (y : @Language.expr L),
      Gamma.derivable Phi y ->
        exists xs : List (@Language.expr L),
          List.Forall Phi xs /\ Gamma.derivable (fun x => x ∈ xs) y

theorem deduction_weaken {L : Language.{u}} [Gamma : Derivable L]
    [bSC : BasicSequentCalculus L Gamma]
    (Phi Psi : context (L := L)) (x : @Language.expr L) :
    Included _ Phi Psi -> derivable (L := L) Phi x -> derivable (L := L) Psi x :=
  bSC.deduction_weaken Phi Psi x

theorem derivable_assum {L : Language.{u}} [Gamma : Derivable L]
    [bSC : BasicSequentCalculus L Gamma]
    (Phi : context (L := L)) (x : @Language.expr L) :
    In _ Phi x -> derivable (L := L) Phi x :=
  bSC.derivable_assum Phi x

theorem deduction_subst {L : Language.{u}} [Gamma : Derivable L]
    [bSC : BasicSequentCalculus L Gamma]
    (Phi Psi : context (L := L)) (y : @Language.expr L) :
    (forall x, Psi x -> derivable (L := L) Phi x) ->
      derivable (L := L) (Union _ Phi Psi) y -> derivable (L := L) Phi y :=
  bSC.deduction_subst Phi Psi y

theorem derivable_finite_witnessed {L : Language.{u}} [Gamma : Derivable L]
    [fwSC : FiniteWitnessedSequentCalculus L Gamma]
    (Phi : context (L := L)) (y : @Language.expr L) :
    derivable (L := L) Phi y ->
      exists xs : List (@Language.expr L),
        List.Forall Phi xs /\ derivable (L := L) (fun x => x ∈ xs) y :=
  fwSC.derivable_finite_witnessed Phi y

section DerivableRulesFromSequentCalculus

variable {L : Language.{u}} [Gamma : Derivable L] [bSC : BasicSequentCalculus L Gamma]

theorem deduction_subst1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      derivable (L := L) Phi x -> derivable (L := L) (Phi ;; x) y ->
        derivable (L := L) Phi y := by
  intro Phi x y hPx hPxy
  exact deduction_subst Phi (Singleton _ x) y
    (by
      intro z hz
      cases hz
      exact hPx)
    hPxy

theorem derivable_trans :
    forall (Phi Psi : context (L := L)) (y : @Language.expr L),
      (forall x, Psi x -> derivable (L := L) Phi x) ->
        derivable (L := L) Psi y -> derivable (L := L) Phi y := by
  intro Phi Psi y hPsiDer hDer
  exact deduction_subst Phi Psi y hPsiDer
    (deduction_weaken Psi (Union _ Phi Psi) y
      (right_Included_Union Phi Psi)
      hDer)

theorem deduction_weaken1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      derivable (L := L) Phi y -> derivable (L := L) (Phi ;; x) y := by
  intro Phi x y hDer
  exact deduction_weaken Phi (Phi ;; x) y
    (by
      intro z hz
      exact Or.inl hz)
    hDer

theorem derivable_assum1 :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      derivable (L := L) (Phi ;; x) x := by
  intro Phi x
  exact derivable_assum (Phi ;; x) x (Or.inr rfl)

theorem contextual_derivable_finite_witnessed
    [fwSC : FiniteWitnessedSequentCalculus L Gamma] :
    forall (Phi Psi : context (L := L)) (y : @Language.expr L),
      derivable (L := L) (Union _ Phi Psi) y ->
        exists xs : List (@Language.expr L),
          List.Forall Psi xs /\
            derivable (L := L) (Union _ Phi (fun x => x ∈ xs)) y := by
  exact DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed
    (by
      intro Phi Psi x hInc hDer
      exact deduction_weaken Phi Psi x hInc hDer)
    (by
      intro Phi y hDer
      exact derivable_finite_witnessed Phi y hDer)

end DerivableRulesFromSequentCalculus

syntax "solve_assum" : tactic

macro_rules
  | `(tactic| solve_assum) =>
      `(tactic|
        first
        | assumption
        | apply derivable_assum1
        | apply derivable_assum <;> assumption
        | apply deduction_weaken <;> assumption
        | apply deduction_weaken1; solve_assum
        | fail "Cannot find the conclusion in assumption")

theorem WeakSubst12BasicSequentCalculus
    {L : Language.{u}}
    [Gamma : Derivable L]
    [bSC_weak : BasicSequentCalculus_weak L Gamma]
    [bSC_subst : BasicSequentCalculus_subst L Gamma] :
    BasicSequentCalculus L Gamma := by
  constructor
  · intro Phi Psi x hInc hDer
    exact BasicSequentCalculus_weak.__deduction_weaken Phi Psi x hInc hDer
  · intro Phi x hIn
    exact BasicSequentCalculus_weak.__derivable_assum Phi x hIn
  · intro Phi Psi y hPsiDer hDer
    exact BasicSequentCalculus_subst.__deduction_subst Phi Psi y hPsiDer hDer

end Unifysl
