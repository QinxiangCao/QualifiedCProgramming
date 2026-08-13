import Unifysl.GeneralLogic.Base

/-!
Coq inventory from `GeneralLogic/ProofTheory/TheoryOfSequentCalculus.v`:
- Properties: `DerivableRefl`, `DeductionWeaken`, `DerivableAssu`,
  `DeductionSubst1`, `DeductionSubst`, `DerivableFiniteWitnessed`,
  `ContextualDerivableFiniteWitnessed`.
- Lemmas:
  `DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed`,
  `DeductionWeaken_ContextualDerivableFiniteWitnessed_2_DerivableFiniteWitnessed`,
  `DeductionSubst_2_DeductionSubst1`,
  `DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst`,
  `DerivableRefl_DeductionWeaken_2_DerivableAssu`,
  `DerivableAssu_2_DerivableRefl`.
- Generator classes: `BasicSequentCalculus_weak`,
  `BasicSequentCalculus_subst1`, `BasicSequentCalculus_subst`,
  `BasicSequentCalculus_fw`.
- Generator lemma: `Subst1FiniteWitness2Subst`.
-/

universe u v

namespace Unifysl

private theorem list_forall_impl {A : Type v} {P Q : A -> Prop}
    (h : forall x, P x -> Q x) :
    forall {xs : List A}, List.Forall P xs -> List.Forall Q xs
  | [], List.Forall.nil => List.Forall.nil
  | x :: _, List.Forall.cons hx hxs =>
      List.Forall.cons (h x hx) (list_forall_impl h hxs)

private theorem split_union_forall {A : Type v} (Phi Psi : A -> Prop) :
    forall {xs : List A},
      List.Forall (Union A Phi Psi) xs ->
        exists xs' : List A,
          (forall x, x ∈ xs -> Phi x \/ x ∈ xs') /\ List.Forall Psi xs'
  | [], List.Forall.nil =>
      ⟨[], by
        constructor
        · intro x hx
          cases hx
        · exact List.Forall.nil⟩
  | x :: _, List.Forall.cons hx htail =>
      match split_union_forall Phi Psi htail with
      | ⟨xs', hmem, hpsi⟩ =>
          match hx with
          | Or.inl hPhi =>
              ⟨xs', by
                constructor
                · intro z hz
                  cases hz with
                  | head =>
                      exact Or.inl hPhi
                  | tail _ hzTail =>
                      exact hmem z hzTail
                · exact hpsi⟩
          | Or.inr hPsi =>
              ⟨x :: xs', by
                constructor
                · intro z hz
                  cases hz with
                  | head =>
                      exact Or.inr (List.Mem.head xs')
                  | tail _ hzTail =>
                      cases hmem z hzTail with
                      | inl hPhi => exact Or.inl hPhi
                      | inr hIn => exact Or.inr (List.Mem.tail _ hIn)
                · exact List.Forall.cons hPsi hpsi⟩

section PropertiesOfSequentCalculus

def DerivableRefl (L : Language.{u}) (Gamma : Derivable L) : Prop :=
  forall x : @Language.expr L,
    Gamma.derivable ((empty_context (L := L)) ;; x) x

def DeductionWeaken (L : Language.{u}) (Gamma : Derivable L) : Prop :=
  forall (Phi Psi : context (L := L)) (x : @Language.expr L),
    Included _ Phi Psi -> Gamma.derivable Phi x -> Gamma.derivable Psi x

def DerivableAssu (L : Language.{u}) (Gamma : Derivable L) : Prop :=
  forall (Phi : context (L := L)) (x : @Language.expr L),
    In _ Phi x -> Gamma.derivable Phi x

def DeductionSubst1 (L : Language.{u}) (Gamma : Derivable L) : Prop :=
  forall (Phi : context (L := L)) (x y : @Language.expr L),
    Gamma.derivable Phi x -> Gamma.derivable (Phi ;; x) y -> Gamma.derivable Phi y

def DeductionSubst (L : Language.{u}) (Gamma : Derivable L) : Prop :=
  forall (Phi Psi : context (L := L)) (y : @Language.expr L),
    (forall x, Psi x -> Gamma.derivable Phi x) ->
      Gamma.derivable (Union _ Phi Psi) y -> Gamma.derivable Phi y

def DerivableFiniteWitnessed (L : Language.{u}) (Gamma : Derivable L) : Prop :=
  forall (Phi : context (L := L)) (y : @Language.expr L),
    Gamma.derivable Phi y ->
      exists xs : List (@Language.expr L),
        List.Forall Phi xs /\ Gamma.derivable (fun x => x ∈ xs) y

def ContextualDerivableFiniteWitnessed (L : Language.{u}) (Gamma : Derivable L) : Prop :=
  forall (Phi Psi : context (L := L)) (y : @Language.expr L),
    Gamma.derivable (Union _ Phi Psi) y ->
      exists xs : List (@Language.expr L),
        List.Forall Psi xs /\ Gamma.derivable (Union _ Phi (fun x => x ∈ xs)) y

end PropertiesOfSequentCalculus

section TheoryOfSequentCalculus

variable {L : Language.{u}} [Gamma : Derivable L]

theorem DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed :
    DeductionWeaken L Gamma ->
    DerivableFiniteWitnessed L Gamma ->
    ContextualDerivableFiniteWitnessed L Gamma := by
  intro hWeak hFW Phi Psi y hDer
  rcases hFW (Union _ Phi Psi) y hDer with ⟨xs, hxsAll, hxsDer⟩
  have hsplit := split_union_forall Phi Psi hxsAll
  rcases hsplit with ⟨xs', hmem, hpsi⟩
  exact ⟨xs', hpsi, hWeak (fun x => x ∈ xs) (Union _ Phi (fun x => x ∈ xs')) y
    (by
      intro z hz
      exact hmem z hz)
    hxsDer⟩

theorem DeductionWeaken_ContextualDerivableFiniteWitnessed_2_DerivableFiniteWitnessed :
    DeductionWeaken L Gamma ->
    ContextualDerivableFiniteWitnessed L Gamma ->
    DerivableFiniteWitnessed L Gamma := by
  intro hWeak hCFW Phi y hDer
  have hUnionDer : Union _ (empty_context (L := L)) Phi |--- y :=
    hWeak Phi (Union _ (empty_context (L := L)) Phi) y
      (by
        intro z hz
        exact Or.inr hz)
      hDer
  rcases hCFW (empty_context (L := L)) Phi y hUnionDer with ⟨xs, hxsAll, hxsDer⟩
  exact ⟨xs, hxsAll, hWeak (Union _ (empty_context (L := L)) (fun x => x ∈ xs))
    (fun x => x ∈ xs) y
    (by
      intro z hz
      cases hz with
      | inl hEmpty => cases hEmpty
      | inr hMem => exact hMem)
    hxsDer⟩

theorem DeductionSubst_2_DeductionSubst1 :
    DeductionSubst L Gamma ->
    DeductionSubst1 L Gamma := by
  intro hSubst Phi x y hPx hPxy
  exact hSubst Phi (Singleton _ x) y
    (by
      intro z hz
      cases hz
      exact hPx)
    hPxy

theorem DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst :
    DeductionWeaken L Gamma ->
    ContextualDerivableFiniteWitnessed L Gamma ->
    DeductionSubst1 L Gamma ->
    DeductionSubst L Gamma := by
  intro hWeak hCFW hSubst1 Phi Psi y hPsiDer hDer
  rcases hCFW Phi Psi y hDer with ⟨xs, hxsPsi, hxsDer⟩
  have hxsDerivable : List.Forall (fun x => Phi |--- x) xs :=
    list_forall_impl hPsiDer hxsPsi
  have eliminate :
      forall xs : List (@Language.expr L),
        List.Forall (fun x => Phi |--- x) xs ->
          (Union _ Phi (fun z => z ∈ xs) |--- y) -> (Phi |--- y) := by
    intro xs
    induction xs with
    | nil =>
        intro _ hDerNil
        exact hWeak (Union _ Phi (fun z => z ∈ ([] : List (@Language.expr L)))) Phi y
          (by
            intro z hz
            cases hz with
            | inl hPhi => exact hPhi
            | inr hMem => cases hMem)
          hDerNil
    | cons x xs ih =>
        intro hall hDerCons
        cases hall with
        | cons hx htail =>
            apply ih htail
            exact hSubst1 (Union _ Phi (fun z => z ∈ xs)) x y
              (hWeak Phi (Union _ Phi (fun z => z ∈ xs)) x
                (by
                  intro z hz
                  exact Or.inl hz)
                hx)
              (hWeak (Union _ Phi (fun z => z ∈ x :: xs))
                ((Union _ Phi (fun z => z ∈ xs)) ;; x) y
                (by
                  intro z hz
                  cases hz with
                  | inl hPhi =>
                      exact Or.inl (Or.inl hPhi)
                  | inr hMem =>
                      cases hMem with
                      | head =>
                          exact Or.inr rfl
                      | tail _ hTail =>
                          exact Or.inl (Or.inr hTail))
                hDerCons)
  exact eliminate xs hxsDerivable hxsDer

theorem DerivableRefl_DeductionWeaken_2_DerivableAssu :
    DerivableRefl L Gamma ->
    DeductionWeaken L Gamma ->
    DerivableAssu L Gamma := by
  intro hRefl hWeak Phi x hIn
  exact hWeak ((empty_context (L := L)) ;; x) Phi x
    (by
      intro z hz
      cases hz with
      | inl hEmpty => cases hEmpty
      | inr hSingleton =>
          cases hSingleton
          exact hIn)
    (hRefl x)

theorem DerivableAssu_2_DerivableRefl :
    DerivableAssu L Gamma ->
    DerivableRefl L Gamma := by
  intro hAssu x
  exact hAssu ((empty_context (L := L)) ;; x) x (Or.inr rfl)

end TheoryOfSequentCalculus

section TheoryOfSequentCalculusForGenerator

class BasicSequentCalculus_weak (L : Language.{u}) (Gamma : Derivable L) : Prop where
  __deduction_weaken :
    forall (Phi Psi : context (L := L)) (x : @Language.expr L),
      Included _ Phi Psi -> Gamma.derivable Phi x -> Gamma.derivable Psi x
  __derivable_assum :
    forall (Phi : context (L := L)) (x : @Language.expr L),
      In _ Phi x -> Gamma.derivable Phi x

class BasicSequentCalculus_subst1 (L : Language.{u}) (Gamma : Derivable L) : Prop where
  __deduction_subst1 :
    forall (Phi : context (L := L)) (x y : @Language.expr L),
      Gamma.derivable Phi x -> Gamma.derivable (Phi ;; x) y -> Gamma.derivable Phi y

class BasicSequentCalculus_subst (L : Language.{u}) (Gamma : Derivable L) : Prop where
  __deduction_subst :
    forall (Phi Psi : context (L := L)) (y : @Language.expr L),
      (forall x, Psi x -> Gamma.derivable Phi x) ->
        Gamma.derivable (Union _ Phi Psi) y -> Gamma.derivable Phi y

class BasicSequentCalculus_fw (L : Language.{u}) (Gamma : Derivable L) : Prop where
  __derivable_finite_witnessed :
    forall (Phi : context (L := L)) (y : @Language.expr L),
      Gamma.derivable Phi y ->
        exists xs : List (@Language.expr L),
          List.Forall Phi xs /\ Gamma.derivable (fun x => x ∈ xs) y

theorem Subst1FiniteWitness2Subst
    {L : Language.{u}}
    [Gamma : Derivable L]
    [bSC_weak : BasicSequentCalculus_weak L Gamma]
    [bSC_subst1 : BasicSequentCalculus_subst1 L Gamma]
    [bSC_fw : BasicSequentCalculus_fw L Gamma] :
    BasicSequentCalculus_subst L Gamma := by
  constructor
  exact DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst
    (by
      intro Phi Psi x hInc hDer
      exact BasicSequentCalculus_weak.__deduction_weaken Phi Psi x hInc hDer)
    (DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed
      (by
        intro Phi Psi x hInc hDer
        exact BasicSequentCalculus_weak.__deduction_weaken Phi Psi x hInc hDer)
      (by
        intro Phi y hDer
        exact BasicSequentCalculus_fw.__derivable_finite_witnessed Phi y hDer))
    (by
      intro Phi x y hPx hPxy
      exact BasicSequentCalculus_subst1.__deduction_subst1 Phi x y hPx hPxy)

end TheoryOfSequentCalculusForGenerator

end Unifysl
